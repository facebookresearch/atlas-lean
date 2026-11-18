# Agent guidance for ATLAS

User instructions override this file.

- [README.md](README.md) maps the libraries: `MathlibExt`, `CSLibExt`,
  `PhyslibExt`, `WantedExt` and their test libraries.
  [REVIEWING.md](REVIEWING.md) is the rubric every PR is reviewed against,
  and [CONTRIBUTING.md](CONTRIBUTING.md) covers copyright headers and the CLA.
- The ATLAS wiki under `blueprint/` is the graph of the library's plan.
  [docs/BLUEPRINT.md](docs/BLUEPRINT.md) gives its
  [rules](docs/BLUEPRINT.md#graph-rules) and explains how to build and sync it.
- Work is tracked as GitHub issues: `task:formalize`, one per Lean module with
  ready results, and `task:dag-work`, one per node to expand.

## Skills

| Skill | Use it to |
| --- | --- |
| [atlas-solve-issue](.agents/skills/atlas-solve-issue/SKILL.md) | pick up a task issue, take it, and carry its PR through review to merge |
| [atlas-graph-pr](.agents/skills/atlas-graph-pr/SKILL.md) | change the graph, including expanding a node marked unexpanded |

`.claude/skills` links to the same folder for Claude Code.

## Before you open a PR

- Run `scripts/check.sh` from the repository root. If you changed
  `blueprint/`, also run `python scripts/check_graph_rules.py --base origin/main`.
- Work one issue per PR, and reference it in the body (`Closes #<issue>`, or
  `Part of #<issue>` for part of a module's list).
- Address every Codex finding before you ask for human review.
