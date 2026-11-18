---
name: atlas-graph-pr
description: >-
  Make a pull request that changes the ATLAS graph (blueprint/roadmap/,
  blueprint/links/, scripts/taxonomy.json): expand a node marked unexpanded,
  add or move pages, edit statements, or add informal edges. Use for any
  task:dag-work issue, and whenever a PR touches the wiki.
---

# Make a graph PR

The rules are the [graph rules](../../../docs/BLUEPRINT.md#graph-rules), each
with its reason, and reviewers apply them from
[REVIEWING.md](../../../REVIEWING.md#wiki-and-graph-prs). Read both before you
change anything. This skill only gives the order of work.

## 1. Start from the issue

- A graph PR works one issue. For DAG work, that is a `task:dag-work` issue
  naming one node marked `"org.atlas-wiki": {"unexpanded": true}` in its
  annotation. Take the issue before you start, as
  [atlas-solve-issue](../atlas-solve-issue/SKILL.md) describes.
- Branch from the latest `main` and keep the PR to that issue.

## 2. Find what exists

Before adding a page or a statement, search for it. A duplicate is the most
common review finding.

```sh
autoform search blueprint "<words from the statement>"
git grep -n "<a likely Lean name>" -- MathlibExt CSLibExt PhyslibExt WantedExt
```

Search pinned Mathlib too. A result Mathlib already has gets no new
statement; link the existing page instead.

## 3. Make the change

**Expanding a node (DAG work):**

1. Read the node's page, its sources, and its parent folder page. Decide on
   children that each fit one PR of work. Leaf statements are usually a lemma
   or a definition, a few hundred lines of Lean at most.
2. Write each low-level child as a `theorem_wanted` (a result) or
   `def_wanted` (a definition) in the matching `WantedExt` module, with a
   docstring. The docstring's first sentence is the page's statement. Add a
   `Source:` line for the reference. The module must import
   `Batteries.Util.ProofWanted` directly ([WantedExt/README.md](../../../WantedExt/README.md)).
3. Run `python scripts/sync_wiki.py declarations` to write the children's
   pages, then edit their prose. Never hand-write a page for a declaration.
4. Write each child that is still high-level as a new page with no
   declaration, and give its annotation the `unexpanded` marker. Its page says
   what it covers and which sources it follows.
5. Remove the marker from the node you expanded. It becomes the folder page
   that lists its children.
6. Give the new marked nodes their prerequisites with their own
   `## Depends on` (rule 10), which counts toward readiness. The Lean orders
   the wanted statements. Use `## Informally uses` only for what a source
   cites but the mathematics doesn't need.

**Other graph edits:**

- Moving a page or folder: `autoform move blueprint OLD NEW`, plus the
  `scripts/taxonomy.json` placement in the same PR.
- A statement on a page must match its declaration, hypotheses and
  conventions included (`x / 0 = 0`, truncated subtraction, `[NeZero q]`).
  Fix the Lean docstring on `main` too (rule 7).

On a page tied to a declaration, never commit `## Depends on` or `## Proof
depends on`, and never commit `site/`, `site-src/` or the dependency dump. The
build writes them.

## 4. Check locally

```sh
python scripts/check_graph_rules.py --base origin/main
python -m unittest scripts.test_check_graph_rules
autoform check blueprint
lake build WantedExt        # when you added wanted statements
scripts/check.sh preflight
```

Install Autoform as [docs/BLUEPRINT.md](../../../docs/BLUEPRINT.md) shows, at the
commit in `.github/autoform-ref`.

## 5. Open the PR

- Title: what changes in the graph, for example "Expand Hodge theory into its
  first results".
- Body: `Closes #<issue>`, the nodes added or changed, and for an expansion,
  why these children and this granularity.
- Keep it under 3,000 files. Split a large change by subject.
- A graph PR needs a code owner's approval as well as Codex's. Reply to every
  Codex finding: fix it and push, or explain with evidence why it does not
  apply. Then follow the PR through to merge, as
  [atlas-solve-issue](../atlas-solve-issue/SKILL.md) describes.
