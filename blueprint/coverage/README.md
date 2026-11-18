---
kind: coverage
status: in-progress
---

# ATLAS coverage

Each documented public declaration of the ATLAS v2 libraries gets one roadmap
article, which `scripts/sync_wiki.py declarations` writes from its docstring. The
counts below are of documented declarations, so they include any whose article that
sync has yet to write. The standalone `Atlas/` developments are not decomposed yet,
and the archived v1 release is not part of the wiki. Progress percentages and target
counts cover only the decomposed rows below; they are not repository-wide coverage.

| Area | Coverage | Evidence |
| --- | --- | --- |
| v2 / MathlibExt | DECOMPOSED | [27834 documented public declarations](../roadmap/README.md) across 28 subjects; 378 instances and 6009 undocumented public declarations are not articles. |
| v2 / CSLibExt | DECOMPOSED | [18336 documented public declarations](../roadmap/README.md) across 10 subjects; 348 instances and 5010 undocumented public declarations are not articles. |
| v2 / PhyslibExt | DECOMPOSED | [4787 documented public declarations](../roadmap/README.md) across 7 subjects; 112 instances and 5262 undocumented public declarations are not articles. |
| v2 / WantedExt | DECOMPOSED | [28594 documented public declarations](../roadmap/README.md) across 27 subjects; 282 instances and 334 undocumented public declarations are not articles. |
| v2 tests (MathlibExtTest, CSLibExtTest, PhyslibExtTest) | OUT | Tests and diagnostics rather than mathematical results. |
| Atlas/StatisticalMechanics | MAPPED | Standalone Lean files; no roadmap articles yet. |
| Atlas/FC | MAPPED | Standalone Lean files; no roadmap articles yet. |
| Atlas/CPythonListsort | OUT | Maintained as its own Autoform blueprint inside Atlas/CPythonListsort. |
