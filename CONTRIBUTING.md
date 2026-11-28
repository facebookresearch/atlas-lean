# Contributing to ATLAS

We want to make contributing to this project as easy and transparent as
possible.

## Ways to help

People and agents work on ATLAS side by side, and writing Lean is only one way
to help:

- **Formalize a result.** Take a statement to write in Lean or to prove
  ([Picking a task](#picking-a-task)) and open a pull request.
- **Check a page.** Compare it with its source and, when it links a Lean
  declaration, with that declaration too: Lean checks proofs, not whether a
  statement means what was intended, so this takes readers. A page with no
  Lean link is checked against its source alone; its declaration may not exist
  yet, or may be held back until a known problem is fixed
  ([Writing pages](docs/BLUEPRINT.md#writing-pages)). Search the open issues,
  then
  [report a page problem](https://github.com/facebookresearch/atlas-lean/issues/new?template=page-problem.yml);
  [Mathematical faithfulness](REVIEWING.md#mathematical-faithfulness) lists
  what to compare. The pull request that fixes it says `Closes #…`.
- **Review an area against a source.** Each open
  [`source-review`](https://github.com/facebookresearch/atlas-lean/labels/source-review)
  issue names a source and the folders to start from: add the source's central
  definitions and results that the graph lacks, check the existing pages
  against it, and propose the changes as pull requests. Where the issue and the
  [graph rules](docs/BLUEPRINT.md#graph-rules) differ, follow the rules and say
  so in the pull request.
- **Propose a target.** To ask for results the site lacks,
  [propose a target](https://github.com/facebookresearch/atlas-lean/issues/new?template=target.yml):
  give a source for each result and say what has to be on the site for the
  issue to close. For whole areas, see the roadmaps labelled
  [`community-roadmap`](https://github.com/facebookresearch/atlas-lean/labels/community-roadmap)
  (contributed by collaborators) and
  [`tauceti-roadmap`](https://github.com/facebookresearch/atlas-lean/labels/tauceti-roadmap)
  (to bring in from Tau Ceti).
- **Improve the tools and the agent skills.** Pull requests to `scripts/`, the
  workflows, [`AGENTS.md`](AGENTS.md) and the skills in `.agents/skills/`
  follow the steps below. A maintainer approves a change to `.github/`,
  `REVIEWING.md`, `AGENTS.md`, `.agents/` or `.claude/` before it is queued:
  these files steer CI, the automated reviews and the agents that work here.
- **Build on the data.** The site publishes
  [`tasks.json`](https://facebookresearch.github.io/atlas-lean/tasks.json) and
  [`dependencies/index.json`](https://facebookresearch.github.io/atlas-lean/dependencies/index.json):
  the ready tasks, and every node of the dependency explorer with its status
  and its relations. Both are public; their formats can still change.

## Picking a task

The [site](https://facebookresearch.github.io/atlas-lean/) lists the
formalization tasks that are ready now: statements to write in Lean and
statements to prove, as `autoform work` finds them
([What the tools own](docs/BLUEPRINT.md#what-the-tools-own)). It publishes
them as
[`tasks.json`](https://facebookresearch.github.io/atlas-lean/tasks.json), which
each `main` build writes with `autoform work list --json`, together with the
commit it was computed from. You don't need to build the repository to pick
one, and people and agents follow the same steps:

1. Take a task from `tasks.json`. `python3 scripts/next_task.py` prints the
   next ones, with a GitHub token in `GH_TOKEN`; `--json` prints them for
   agents. It prints the statements to write first, then the tasks by
   [priority](#which-areas-come-first).
2. Skip a task that an open pull request names, by its article id (`af_…`) or
   its Lean declaration, in its title, body or branch. `next_task.py` skips
   those, including those an older pull request names, in its title, branch or
   code, by the end of a declaration's name that no other task shares, and the
   tasks of pull requests merged into `main` since `tasks.json` was computed.
3. Open a draft pull request early, with the task's article id in its body, so
   that others see the task is taken. Mark it ready for review when it is done,
   or close it if you stop.

Graph-building tasks are on the same list: `next_task.py --graph` also prints
the next [nodes still to expand](docs/BLUEPRINT.md#nodes-still-to-expand),
which each `main` build publishes as
[`graph-tasks.json`](https://facebookresearch.github.io/atlas-lean/graph-tasks.json)
with `tasks.json`'s commit, and skips those that a pull request names by their
node id or page path. Take one the same way, with a draft pull request that
names its node id. Read the page's `## Expansion` section first: a page
imported from mathgraph may only need a missing link
([Pages imported from mathgraph](docs/BLUEPRINT.md#pages-imported-from-mathgraph)),
and other nodes are expanded as
[Expanding a node](docs/BLUEPRINT.md#expanding-a-node) says.

Proving a task needs a built checkout. `lake exe cache get` fetches only
Mathlib's build, and ATLAS's own modules take hours to build from source, so
start from CI's build of `main` instead. It needs a `gh` login, `zstd` and
about 15 GB free:

```sh
lake exe cache get    # Mathlib
scripts/get_build.sh  # ATLAS, from CI's build of the nearest commit of main
lake build            # what changed since
```

### Which areas come first

[`blueprint/priorities.json`](blueprint/priorities.json) weighs the areas of
the graph so that ATLAS and [Tau Ceti](https://github.com/TauCetiProject/TauCetiRoadmap)
complement each other: 2 for an area ATLAS takes first, where Tau Ceti has
few or no roadmaps (applications, computer science, discrete mathematics,
probability), 1 as usual, and 0.5 for one it leaves for later, as Tau Ceti's
roadmaps already cover it. A weight belongs to a subject (`Combinatorics`) or
a field (`NumberTheory/zeta-l-functions`) of `scripts/taxonomy.json`, named as
its folder under `blueprint/roadmap/`, which starts the node ids of the tasks
under it; a field's weight overrides its subject's, and `default` gives the
others theirs.
`next_task.py` lists the statements to write first, then the proofs; within
each, the free tasks of higher weight come first, and those of equal weight in
`tasks.json`'s order. `--priorities` reads another file, or a URL.
Tools that pick tasks their own way can call its `load_priorities` and
`priority`. The weights change by pull request, like the code.

## Pull Requests
We actively welcome your pull requests.

1. Fork the repo and create your branch from `main`.
2. If you've added code that should be tested, add tests.
3. If you've changed APIs, update the documentation.
4. Ensure the test suite passes.
5. Make sure your code lints.
6. If you haven't already, complete the Contributor License Agreement ("CLA").

### Claim the work you start

Many people and agents open pull requests here at once. Claim a substantial
piece of work before you start it, so that others can steer around it:

- **Open a draft pull request** when you start, as
  [Picking a task](#picking-a-task) says. Its title names the topic, and its
  description names each ready task it takes by article id, on a line
  `Tasks: af_…`. When the work takes on an issue, such as a source-review
  issue, a page problem or a target, also comment on the issue that you are
  working on it, with a link to the draft. The draft claims its tasks until it
  is closed: mark it ready for review when it is done, or close it if you stop
  and then say so on any issue you commented on. If a draft that names a task
  you want has had no push for a week, ask on it whether its author goes on.
- **Or open an issue** whose title starts with `[Claim]` and that names the
  area, the modules or the task ids you are taking, for work that spans several
  pull requests. It is a claim while it is open and has been updated in the
  last 30 days: comment on it to renew it, and close it to release it. Link it
  from each pull request that continues it.

Look for an open pull request and an active `[Claim]` issue that cover the work
before you start, and read the comments on the work's issue if it has one;
`next_task.py` skips the tasks that open pull requests name, but does not read
issues. A pull request that only cites a tracking issue, as the proofs of ready
statements cite
[#6002](https://github.com/facebookresearch/atlas-lean/issues/6002), does not
take it on and leaves no comment there: the issue's page lists the pull
requests that cite it. When two claims cover the same task, the one that has
been active longer without a break keeps it; a pull request that continues an
active `[Claim]` issue counts from the issue. A claim only saves duplicated
work: it reserves nothing else, and anyone may still review, fix or improve
merged code.

To update a branch that someone else may also push to, such as another
contributor's pull request, push a fast-forward of the tip you fetched. If you
must rewrite it, use
`git push --force-with-lease=<branch>:<tip you fetched> <remote> HEAD:<branch>`,
which refuses the rewrite if the branch no longer points at the tip you
fetched.

### Lean pull requests and graph pull requests

A pull request changes the Lean or the graph:

- **Lean side:** Lean files and their rows in `provenance/`. A **Lean pull
  request** changes these, and in the graph only what keeps `main`'s links
  whole (below). It runs no sync: the next
  [graph-sync batch](docs/BLUEPRINT.md#graph-sync-batches) gives its new
  documented declarations their pages, annotation rows and folder lists,
  writes their docstring digests, and places the new modules that a `Place:`
  line names or that take a placed module's declarations.
- **Graph side:** everything under `blueprint/`, and `scripts/taxonomy.json`,
  `scripts/wiki-sync.json`, the card move ledger (`scripts/card-moves.jsonl`
  and `scripts/card-moves.d/`) and
  `scripts/mathgraph-map.jsonl`. A **graph pull request** changes the wiki.
  It changes Lean only as the [graph rules](docs/BLUEPRINT.md#graph-rules)
  allow, such as an expansion's wanted statements or the docstring a page's fix
  needs, and then runs the sync for its own declarations
  ([Graph PRs](#graph-prs)). A pull request that changes both Lean and pages is
  a graph pull request in full; split it when you can.
- **What stays coupled:** a Lean pull request that renames, moves or removes a
  declaration updates, in the same pull request, the links, `held` markers and
  `duplicates` entries that name it, and a bump updates the rows of the
  Mathlib-credited pages whose declarations it moves
  ([the next section](#say-how-a-pull-request-touches-the-graph)). Removing a
  page's own declaration with no successor stays a graph change. Provenance
  rows stay with the Lean they describe.
- **Placement:** a new module may say where it goes on a `Place:` line.
  Otherwise the batch gives it the place of the module whose declarations it
  takes, or leaves it in its subject's `not-yet-classified/` folder for an
  editor to place. A module in a folder that is no subject gets pages from a
  `Place:` line in its own pull request; placed later, it needs a sync over the
  whole project to get them.

A **graph-sync batch** is the pull request `scripts/graph_batch.py` makes on
a fresh `main`, one at a time, every one or two hours: a maintainer,
or an agent a maintainer runs, makes it, and someone else reviews it. When no
batch has merged for several hours, any maintainer may make one. So `main`'s
graph trails its Lean by about one batch, plus the batch's review and queue
time; the site, built from `main` once a day, can trail `main` by up to a day
more. Pull requests opened before this rule may land with the graph files they
carry.

Why: of the 379 pull requests merged into `main` from 24 November 18:22 to
25 November 17:04 UTC,

- **Conflicts:** 217 (57%) changed both Lean and graph files, and graph files
  are shared: `scripts/taxonomy.json` was in 55% of all the merges,
  `blueprint/links/` in 18%, folder pages in 16% and `scripts/wiki-sync.json`
  in 13%. One rewrite of `scripts/wiki-sync.json`
  ([#8044](https://github.com/facebookresearch/atlas-lean/pull/8044), 110,062
  of its 110,064 lines) or one large pull request
  ([#7617](https://github.com/facebookresearch/atlas-lean/pull/7617), 2,830
  files) made most open pull requests that carried digests conflict, and
  [#7690](https://github.com/facebookresearch/atlas-lean/pull/7690) appended
  317 lines to one folder page. Lean pull requests now share only the
  provenance files, which were in 59% of the merges.
- **Review:** in 167 of those 217 (77%), the graph change was only
  `scripts/taxonomy.json`, placing new modules. A `Place:` line now carries
  that choice, the batch gives a module that takes a placed module's
  declarations its place, and `scripts/graph_batch.py verify` shows that the
  rest of a batch is exactly the sync's output.
- **CI:** little changes, as Blueprint Pages already built the site for only 47
  of those 217; but a Lean pull request needs no graph check beyond
  `check the graph`, and a batch changes no Lean, so its build has nothing to
  rebuild.
- **Throughput:** Lean pull requests merge without waiting on graph work, as
  most of the 125 Lean-only ones already did: 71 added a module that nothing
  placed, with no page.

### Say how a pull request touches the graph

Each pull request description has one `Graph:` line, which ties its Lean to
the [graph](docs/BLUEPRINT.md#graph-rules). It lists the article ids (`af_…`)
of the pages the pull request proves, fixes or extends, such as the ready tasks
it takes, and adds `new` when it adds documented declarations, which get pages
under [Maintaining articles](docs/BLUEPRINT.md#maintaining-articles). It is
`Graph: none` only when the pull request changes nothing the graph shows, and
`Graph: batch` on a graph-sync batch.

- **A new module may say where it goes.** Add a line for it after the `Graph:`
  line, `Place: <module> -> <field>`, or `Place: <module> -> <field> | <topic>`
  to name its topic, with the module as a path without `.lean` and a field or
  subfield of `scripts/taxonomy.json`:

  ```text
  Place: MathlibExt/Algebra/Ring/Idempotents -> Algebra/rings-and-fields
  ```

  Write it as a plain line of the description, as the `Graph:` line is: the
  batch reads only the lines that GitHub shows as plain text, none in a code
  block, a list, a quotation or a comment. A topic is one line of at most 160
  characters with none of ``<>[]{}|`\@#`` and no address (`://`). Give a line
  to each new module that takes no placed module's declarations when you know
  its field, and always to a module in a folder that is no subject, one that
  neither the taxonomy nor `generate_wiki.LIBRARIES` maps to one: it gets no
  pages without one. The batch reads the line once the pull request has merged
  ([Graph-sync batches](docs/BLUEPRINT.md#graph-sync-batches)), so write it
  before then and don't edit the description afterwards: the batch leaves out
  every `Place:` line of a description edited after the merge. It also leaves
  out, with a note, one for a module whose pages are already outside the topic
  it names: moving them is a graph pull request's. Leave
  `scripts/taxonomy.json` as it is.
- **A renamed, moved or removed declaration keeps its pages.** In the same pull
  request, point each link to it at its successor, keeping every article id. A
  link that is only a reference may instead be removed: the page keeps its own
  declaration. Update or remove a `held` marker or a `duplicates` entry that
  names it in the same way, and a Lean or Mathlib bump updates the row of a
  Mathlib-credited page whose declaration it moves
  ([Mathlib-credited pages](docs/BLUEPRINT.md#mathlib-credited-pages)). These
  edits keep a Lean pull request a Lean pull request. `check the graph` fails
  on a link to a declaration the Lean lacks; a `held` marker or `duplicates`
  entry left naming one is reported only by the advisory `graph sync`, and stops
  every batch until it is fixed, so fix it here.
- **A page's own declaration removed with no successor** leaves a planned page
  ([Writing pages](docs/BLUEPRINT.md#writing-pages)), which needs its own
  prerequisites: remove the declaration in a graph pull request that unlinks
  the page and writes them.
- **A changed docstring** of a declaration that has a page: `graph sync` lists
  the page, to check. If it no longer says what the declaration states, fix it
  in a graph pull request, or open a
  [page-problem issue](https://github.com/facebookresearch/atlas-lean/issues/new?template=page-problem.yml).
  The batch records the new digest.

### Public references

Files, filenames, branch names, PR titles/descriptions, and complete commit
messages must not contain private task/diff/paste identifiers, private service
links, machine names, or personal workspace paths. Keep private provenance in
private records; use public citations and repository-relative paths here.
Host-path checks accept either slash convention, including doubled backslashes
in string literals and Windows profile-directory casing. Conventional CI
account names `runner` and `runneradmin` are excluded; longer profile names
that start with either word are not. Profile names may contain apostrophes or
Unicode spaces; finding the profile directory is enough to report the path.
A quote immediately after a root is treated as a text boundary, and profile
matches do not cross line breaks. When a path is wrapped in matching double
quotes, single quotes, or backticks, and in filenames, symlink targets, branch
names, and commit header values (identity names included), a profile name that ends the path runs to the closing quote or
the end of the value: only the exact CI account names, an empty name, `.`, and
`..` are exempt there, so `runner!` or `runner.` is reported. In unquoted
prose, sentence punctuation after a root or an exact CI account name is treated
as prose; this is a finite heuristic, not a parser for every file name.
The numeric-reference and campaign-code checks ignore letter case in branch
names and treat underscores as separators. Slashes remain path boundaries;
compound campaign/lesson references have a separate slash-aware pattern, also
checked case-insensitively when quoted in PR text or files.
Dotted roadmap-label checks use the original case and require at least four
upper-case parts; three-part package names and lower-case release branches are
not classified by that shape alone.
Preserve authorship and copyright notices when correcting provenance.

File contents, commit messages (not headers), the message of a supported
embedded merge tag, and PR titles and descriptions recognize two public forms;
filenames, branches, header values, and symlink targets stay strict. A whole
recognized form must lie inside one such message. A publisher identifier is
exempt only in the exact identifier slot of a recognized citation: a DOI under
a listed publisher prefix (optionally prefixed by `doi:` or
`https://doi.org/`) with a valid ISSN check digit, a recognized ScienceDirect
article URL, or an exact citation in the checker.

A filesystem-path match wholly inside an HTTP(S) URL path is exempt only for
a public-looking DNS authority with no user information, valid labels and
port syntax, no local or special-use suffix, and no drive-letter path segment.
Local names, IP literals, and malformed authorities stay strict. A control
character (C0, DEL, or C1) ends the URL path, so text after one is checked.
Other rules still apply inside the URL, and query and fragment text remains
checked.
The checker does not resolve DNS, so a public-looking name is not proof that
its destination is public. New citation forms need a reviewed base-checker
change. These exceptions do not waive other findings or missing inputs.

The **Public references / public-references** check applies to every PR author,
including forks. It reads every outgoing Git commit's complete message and all
headers, including signature-shaped text, plus every new Git file blob. File
versions replaced or deleted before the tip are included. Signature markers
never disable scanning; they are data, not authenticated signatures. File
contents the current base or a public tip still holds, as a file or as a
symlink target, are not re-scanned as file contents; a new or changed symlink
target is scanned strictly, even when its bytes are held as file text. A
single-parent commit that only makes a base-history file executable, with the
same path and bytes, does not have them re-scanned; that skip never counts as a
scan for later commits. New destination filenames are still checked. Editing the
contents or mode of an existing path does not re-report its name. In a merge, a
base-side parent is a direct parent reachable from the base and not contained
in another parent. A name is not re-reported when the current base, a public
tip, or a base-side parent has that exact path, even if the merge changes its
contents or mode.
File contents are scanned unless the current base or a public tip holds the
same bytes (at any path), the merge keeps a base-side parent's exact entry
(same path, mode, and object), or they were already scanned. A retained
symlink target is scanned strictly unless the current base or a public tip
holds it as a symlink target, the merge keeps such an exact entry, or it was
already scanned as a target; a new or changed target is always strict. A
base-side parent's bytes at another path never count. So contents and symlink
targets a merge brings back after the base removed or cleaned them are checked
again, and so is a restored name absent from every base-side parent. The commit
graph cannot tell a deliberate same-path import from an earlier ordinary merge
of a base-side parent, so that parent's exact path and exact entry still pass.
Submodule entries pass only when kept unchanged from the current base or a
public tip. Existing historical
exposures need separate cleanup. It does not
only inspect subjects or added lines. Errors, missing objects, moved PR
metadata, and incomplete ranges fail
the check. It never executes code from the proposed head. PR description edits
rerun it too. LFS pointers, including CRLF and legacy-version forms, fail because
their external contents are not scanned.

Reports contain at most 100 findings, with locations limited to 240 characters.
`findings_truncated: true` means additional findings were omitted. After the
limit is exceeded, reference detection stops, but object and input-completeness
validation continues. A truncated report always fails the check.

To check a local branch before its first push, fetch the public base and scan
its full outgoing range. Put the intended branch name in `pr-metadata.json`
under `branch`; include `title` and `body` if you will also create a PR:

```sh
git fetch origin &&
python3 scripts/check_public_references.py \
  --base "$(git rev-parse origin/main)" --head "$(git rev-parse HEAD)" \
  --metadata pr-metadata.json
```

For an update to an existing public branch, also exclude its already-published
tip. Replace `my-branch` with the remote branch name:

```sh
git fetch origin &&
python3 scripts/check_public_references.py \
  --base "$(git rev-parse origin/main)" --head "$(git rev-parse HEAD)" \
  --public "$(git rev-parse origin/main)" \
  --public "$(git rev-parse origin/my-branch)"
```

`--public` takes a full commit SHA and may be repeated. It excludes published
commit histories, but only entries in each public tip's current tree qualify
for its content and name exemptions. Editing a file under an existing public
name does not force a rename. Removed names, symlinks, and content are checked
again when a push restores them, directly, through a merge, or by building on
an older public commit. New symlink targets are always checked strictly. The
normal base-history behavior is unchanged. This supports forward cleanup,
including updates that merge already-public main and topic tips.

Only pass tips you have fetched from the public repository and verified: the
script checks that each value identifies a commit, not that it is public.
Leave `--public` out for a first push. New outgoing commit headers and
messages, introduced file blobs, new destination paths, and new symlink
targets remain checked.

`--public` excludes Git history only. If you are also creating or changing PR
metadata or a branch name, pass the exact new `title`, `body`, or `branch`
values in a JSON file with `--metadata pr-metadata.json`; supplied fields are
always checked. Unchanged, already-public metadata need not be supplied for
a code-only local pre-push check. The GitHub PR check does not accept
`--public` and still scans the PR's complete range from its base; merge-group
checks likewise remain unchanged. A local pass does not waive a CI finding
or authorize rewriting published history to remove it.

Run the detector's tests with:

```sh
python3 -m unittest discover -s scripts -p 'test_public_references.py'
```

The detector uses identifier/URL/path patterns, not a list of confidential model
names. It is a backstop, not a confidentiality guarantee: unfamiliar private
references, encoded data, images, and compressed archive contents need author
review. Binary files receive a raw-byte text scan, not decompression or OCR.
Legitimate public identifiers can collide with the patterns. In particular,
hyphenated or underscored F-number topics can have the same shape as private
work-item codes. A finding is not proof that the identifier is confidential;
ask maintainers to review such a case rather than disguising the text or
disabling the check. A review accept alone does not change a failing check.
Removing a reference from the tip does not erase already-published history.
CI runs after a branch and PR have been published; run the local check before
pushing to avoid exposing a reference in the first place.

The same job also handles merge-queue events, scanning the complete combined
Git range, including intermediate commits, without executing proposed code.
It pins scanner code to a resolved default-branch commit and checks the queue
ref before and after scanning. PR metadata is checked separately on PR events;
the merge-group route does not enumerate every grouped PR's metadata.

Before making this check required, maintainers must establish trusted workflow
governance. GitHub selects a merge-group workflow definition from the event
ref, and a PR-target workflow from the PR's base branch. Pinning the scanner
does not authenticate the workflow that invokes it. Use a required workflow
from a separately protected source, or enforce trusted review and protection
for all workflow definitions, relevant policy, and default-branch scanner
code. A required job name alone cannot prevent another workflow from reporting
the same name. Verify ordinary PR, fork, and merge-queue delivery after an
authorized deployment before enabling required enforcement. Until then this
is advisory CI, not a standalone merge barrier.

### Graph PRs

A graph PR changes the ATLAS wiki; its content follows the
[graph rules](docs/BLUEPRINT.md#graph-rules). Two kinds of wiki change don't
make a pull request one: a Lean pull request's edits for the declarations it
renames, moves or removes (links, `held` markers, `duplicates` entries and
Mathlib-credited rows; see [Say how a pull request touches the
graph](#say-how-a-pull-request-touches-the-graph)),
whose links `check the graph` checks and whose markers and entries
`graph sync` reports, and a graph-sync batch, which
`scripts/graph_batch.py verify` shows to be exactly what the tools write for
what `main` merged ([Graph-sync batches](docs/BLUEPRINT.md#graph-sync-batches)).
Neither needs an issue, or a code owner's approval unless GitHub requires one;
Codex still reviews them, and a batch's reviewer runs `verify` on its exact
head from an up-to-date checkout of `main`, never from the batch's own branch.
Unlinking a page's own declaration with no successor is not one of them.
When a graph PR's only wiki changes are what `scripts/sync_wiki.py
declarations` writes for its own declarations, as the `graph sync` check
reports, it needs no issue for them, and they need no code owner's approval
unless GitHub requires one; Codex still reviews them. Any other code-owned file
the pull request changes, the sync's own code included, still needs a code
owner's approval. Any other wiki change, a new place in `scripts/taxonomy.json`
included, makes it a graph PR in full.

- **Keep it under 3,000 changed files and name its issue** (`Closes #…` or
  `Part of #…`); a pull request whose only wiki changes are the sync's, as
  above, need not name one. GitHub shows at most 3,000 files in one diff.
- **An expansion changes no Lean outside `WantedExt`,** so its reviewer need
  not also review proofs.
- **Leave what the tools own alone** ([What the tools
  own](docs/BLUEPRINT.md#what-the-tools-own)).
- **A code owner approves it** (`.github/CODEOWNERS`), except the wiki files
  the sync writes, as above, **and Codex reviews it:**
  automatically for the repository's owners, members and collaborators and for
  forks on `codex.yml`'s trusted list; on any other fork PR a maintainer
  comments `@codex` for an advisory review. Agents produce graph changes faster
  than people can check them, and a poor expansion spreads into every task
  below it.
- **A code owner's AI review agent may give the code owner's approval,**
  under the code owner's account, when neither the code owner nor any person
  or agent acting for them authored or committed to the pull request. On a
  pull request that moves shared definitions out of `WantedExt` into a proved
  library (completing a `def_wanted` is not such a move), the agent's approval
  counts only when the moved definitions are unchanged apart from their names,
  namespaces and imports; otherwise a code owner approves it in person. A code
  owner who approves in person says so in the review, as agent and personal
  approvals come from the same account. This rule decides which approvals
  count as a code owner's, not which pull requests need one.

## How PRs merge

`main` takes changes only through GitHub's merge queue; do not push to it
directly. When a PR is ready to merge and its required checks have passed, add
it to the queue. The queue tests it on top of the current `main` and the PRs
queued ahead of it, and adds it to `main` as a merge commit only if the required
checks pass on that combined tree (**Only merge non-failing pull requests**), so
each commit the queue adds to `main`'s first-parent history has passed them on
its own tree.

To queue a standalone PR, use one of:

- **Merge when ready** in the PR's merge box. Someone with write access can
  select it before the checks pass, even while the repository's **Allow
  auto-merge** setting is off; the PR then joins the queue when they pass.
- `gh pr merge <number>`, which needs the repository's **Allow auto-merge**
  setting: on a queue branch, `gh` 2.105.0 asks GitHub to turn on auto-merge,
  which GitHub refuses while that setting is off
  ([cli/cli#13398](https://github.com/cli/cli/issues/13398)). With it on, the
  PR is queued at once if its required checks have passed, and otherwise when
  they pass. `--match-head-commit <sha>` checks the head only when you run the
  command. The queue sets the merge method and the commit message, so
  `--merge`, `--squash`, `--subject` and `--body` have no effect, and `gh`
  refuses `--delete-branch`.
- The GraphQL mutation `enqueuePullRequest` (`pullRequestId`, and
  `expectedHeadOid` to pin the head). It queues the PR only if it can be queued
  now, and otherwise returns an error that says why; it never merges directly.

Before you queue a PR, run `python3 -I scripts/queue/preflight.py <number>` from
an up-to-date checkout of `main`, never from the PR's branch. It prints READY or
NOT READY and what to do next. It checks Codex's approval of the exact head and
the required checks. It checks that CI tested the head on a `main` that has the
current pins, less than 6 hours ago. It checks conflicts with `main` and the
queued PRs, and declarations that a queued PR also adds. With `--enqueue` it
queues a READY PR with `enqueuePullRequest`, pinned to the head it checked. The
[atlas-merge-queue](.agents/skills/atlas-merge-queue/SKILL.md) skill gives the
rules that no check enforces. Never push to a queued PR. Take a PR out of the
middle of the queue only when it is known to be bad. After a bump, check PRs
again before you queue them.

To queue a stack of pull requests (its branches must be in this repository), use
the merge box of the highest PR you want to merge, or `PUT /repos/{owner}/{repo}/pulls/{number}/merge-async` with
`"merge_action": "merge_queue"` on that PR. Either queues that PR together with
every open PR below it in the stack.

`main` refuses direct merges, including those of the REST endpoint
`PUT /repos/{owner}/{repo}/pulls/{number}/merge`, which does not support merge
queues, and of the GraphQL mutation `mergePullRequest`. Scripts and bots should
use `enqueuePullRequest` for a standalone PR, or
`PUT /repos/{owner}/{repo}/pulls/{number}/merge-async` with
`"merge_action": "merge_queue"`, which GitHub requires for a stack of pull
requests; both only ever queue. `merge-async` answers `202` when it accepts the
request, `200` if the PR is already queued or merged, and `409` if another
request is pending; `GET .../merge-async/{uuid}` gives a request's result. A
queue request is not a merge: read the PR's state afterwards to learn whether
it was queued, merged, or removed from the queue.

The queue builds up to 100 merge groups at once, and consecutive PRs that pass
land together, up to 30 at a time; GitHub may exceed that by up to half to keep
a stack together. The queue removes a PR whose required checks fail on its merge
group, or do not conclude within 6 hours; the PR's timeline says why, and the
PRs behind it rebuild without it. In a stack of pull requests, the PRs above it
in the stack leave the queue too. Fix the PR and queue it again. To take a PR
out of the queue, use **Remove from queue** on the PR or on the queue's page, or
the GraphQL mutation `dequeuePullRequest` (for example through `gh api
graphql`); there is no `gh pr` command for it.

The Merge queue retry workflow (`.github/workflows/merge-queue-retry.yml`)
re-runs a merge group's failed jobs once when every failed required check of
that merge group failed for an infrastructure reason (a lost runner, or a
truncated answer or server error from GitHub's API) while the PR is still
queued with it, so that a flaky check does not remove the PR and
restart the builds behind it. It never removes a PR from the queue; for other
failures its run summary only records whether it would have removed the PR
early. It records what it would do, and re-runs nothing, unless the repository
variable `MERGE_QUEUE_RETRY` is `active`.

Queue a Lean or Mathlib bump like any other PR, preferably at a quiet time. With
new pins, CI can fetch Mathlib's cache but must rebuild ATLAS when there is no
matching `.lake/build` cache; the v4.36.0 bump's PR build took 316 minutes.
Merge groups behind the bump can build in parallel but cannot land ahead of it,
and they may repeat that rebuild until a successful `main` build saves a cache
for the new pins.

### Required checks

A PR needs these checks to pass before it can be queued, and again on its merge
group before it merges:

- `repository integrity` (CI): the deterministic repository checks.
- `build` (CI): the Lean build and its policy checks.
- `check the graph` (CI): `autoform check` on the graph as committed, and the
  card move ledger's integrity as the merge commit or merge group combines it,
  against the commit it was made from, with `scripts/card_moves.py check`,
  which reads the ledger's files and Git tree-entry metadata (names, modes and
  types) for regular roadmap `README.md` files, not page contents, and nothing
  else: it fails on rows that break a rule among them, an edited
  frozen file, an edited, renamed or deleted merged fragment, or new fragments
  that interact ([Move ledger](docs/cards.md#move-ledger)). What needs the
  rest of the tree is not required: whether each move ends at a live page of
  its article is the site build's ledger step's, and whether every move since
  the base has its row is `check the cards`'s.
- `source-diagnostics` (Source diagnostics).
- `guard` (Bump guard): the Lean and Mathlib pin check. On a merge group it
  checks a pin change again against the queue's base.

The three workflows that report these five checks are configured for
`pull_request` and `merge_group`, without branch or path filters. If a PR has a merge conflict, resolve it before expecting
its PR checks; a fork PR may also need a maintainer to approve the workflow run.
`scripts/test_merge_queue_checks.py`, run by `scripts/check.sh preflight`,
checks their pull-request and merge-group triggers, filters and concurrency
groups, and that each required check comes from exactly one job, with no
job-level `strategy` and no job-level `if` but the one that skips `build` on
some PRs. CI's `decide which checks to run` job (`scripts/ci_scope.py`) skips
`build` on a PR whose every changed path is graph data (`blueprint/`,
`scripts/taxonomy.json`, `scripts/wiki-sync.json`, `scripts/card-moves.jsonl`,
the move ledger's fragments in `scripts/card-moves.d/`,
`scripts/mathgraph-map.jsonl`) or documentation (Markdown outside `scripts/`
and `.github/`, and `.agents/` and `.claude/`), and a skipped required check
counts as passed. On a PR whose every changed path is graph data, documentation,
a Lean file of the nine libraries or under `provenance/`, `repository integrity`
skips the nine tool test suites of `scripts/test_scripts.sh`, whose tests read
only scripts, workflows and the pins (`ATLAS_TOOL_TESTS`). Merge groups and
pushes to `main` always run every required check, and all of its tests.

The other checks are advisory. Codex does not run on merge groups, but a formal
Codex change request can cancel the PR's CI run while it is still queued or
running; if `build` is cancelled, CI must pass before the PR can be queued. A
completed build is unaffected. `public-references` is configured to run on PRs
and merge groups, but stays advisory until the workflow governance described
under [Public references](#public-references) is in place. `graph sync` is
configured to run on every PR and merge group, without filters. It reports a
link or marker the Lean leaves behind, and whether a graph PR's wiki is in step
with its own Lean
([Maintaining articles](docs/BLUEPRINT.md#maintaining-articles)).
Check workflows and Binary64 conformance are path-filtered on PRs. Blueprint
Pages builds `main` once a day. On a PR, its first job reads the whole diff and
lets the build run only when the PR changes the wiki (`blueprint/`), the import
map, the card move ledger, the tooling that builds and checks the site, the
toolchain pins, a path where the build writes or fetches its outputs, Git
attributes, or a file named like an Autoform output marker; PRs that change
only Lean library files, `scripts/taxonomy.json` or `scripts/wiki-sync.json`
run only its unit tests, in a few minutes, and PRs that change only Lean library
files those tests do not read, provenance and documentation run neither
([GitHub Actions and publication](docs/BLUEPRINT.md#github-actions-and-publication)).
With write access, `gh workflow run blueprint-pages.yml --ref <branch>` builds
and checks a branch on demand; only `main` publishes.

## Lean and Mathlib bumps

Lean, Mathlib, CSLib and Physlib move together to the next final release that
all of them have tagged, and `guard` checks the pins. A bump touches many files
and starts CI from an empty cache, so it follows its own routine, described in
[docs/BUMPS.md](docs/BUMPS.md): one owner keeps the bump branch close to `main`
with `scripts/bump/bump_branch.py`, warms CI's cache with `bump-cache.yml` right
before queueing it, and queues it at the front of the queue at a quiet hour. If
the queue removes your PR just after a bump, merge `main`, fix the PR on the new
toolchain, and queue it again.

## Contributor License Agreement ("CLA")
In order to accept your pull request, we need you to submit a CLA. You only need
to do this once to work on any of Meta's open source projects.

Complete your CLA here: <https://code.facebook.com/cla>

## Issues
We use GitHub issues to track public bugs and the work listed under
[Ways to help](#ways-to-help). For a page problem or a target, use its issue
form. For a bug, please ensure your description is clear and has sufficient
instructions to be able to reproduce it.

Meta has a [bounty program](https://bugbounty.meta.com/) for the safe
disclosure of security bugs. In those cases, please go through the process
outlined on that page and do not file a public issue.

## Coding Style
Lean code follows the
[Mathlib style guide](https://leanprover-community.github.io/contribute/style.html).
`lakefile.toml` turns on Mathlib's standard linter set
(`linter.mathlibStandardSet`) for the five production libraries, minus the
linters it turns off by name, and turns the set off for the four test
libraries. `PhyslibExt` also follows Physlib's conventions
([Library roles](REVIEWING.md#library-roles)).

## Copyright headers
Every Lean file starts with the Meta header:

```lean
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
```

Code from another project keeps that project's copyright notice:

* A file that is mostly copied from another project starts with that project's
  copyright and license header instead (for example, the Apache 2.0 header of
  Formal Conjectures, or the header of the Mathlib file it copies).
* A mostly original file that adapts code from another project keeps the Meta
  header and adds a second block naming each source file, its copyright holder,
  license and authors, for the adapted portions only:

```lean
/-
Portions of this file are adapted from:

`Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean` (Mathlib):
Copyright (c) 2018 Chris Hughes. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
```

CI checks every tracked Lean file with `scripts/check_copyright.py --all` (part of
`scripts/check.sh preflight`); `scripts/check_copyright.py --fix FILE...` adds the
Meta header to files that have none.

## License
By contributing to ATLAS, you agree that your contributions will be licensed
under the LICENSE file in the root directory of this source tree.
