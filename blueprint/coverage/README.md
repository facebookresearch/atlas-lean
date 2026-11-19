---
kind: coverage
status: in-progress
---

# ATLAS coverage

Each documented public declaration of the ATLAS v2 libraries, instances aside, gets one
roadmap article, which `scripts/sync_wiki.py declarations` writes from its docstring; a
declaration the Lean index does not select waits for an editor. The counts below are of
documented non-instance declarations, so they include any whose article that sync has
yet to write. The standalone `Atlas/` developments are not decomposed yet,
and the archived v1 release is not part of the wiki. Progress percentages and target
counts cover only the decomposed rows below; they are not repository-wide coverage.

| Area | Coverage | Evidence |
| --- | --- | --- |
| v2 / MathlibExt | DECOMPOSED | [25846 documented public non-instance declarations](../roadmap/README.md) across 28 subjects; 333 instances and 5751 undocumented public non-instance declarations are not articles. |
| v2 / CSLibExt | DECOMPOSED | [17566 documented public non-instance declarations](../roadmap/README.md) across 7 subjects; 330 instances and 4489 undocumented public non-instance declarations are not articles. |
| v2 / PhyslibExt | DECOMPOSED | [6553 documented public non-instance declarations](../roadmap/README.md) across 6 subjects; 114 instances and 5254 undocumented public non-instance declarations are not articles. |
| v2 / WantedExt | DECOMPOSED | [28175 documented public non-instance declarations](../roadmap/README.md) across 26 subjects; 163 instances and 113 undocumented public non-instance declarations are not articles. |
| v2 tests (MathlibExtTest, CSLibExtTest, PhyslibExtTest) | OUT | Tests and diagnostics rather than mathematical results. |
| Atlas/StatisticalMechanics | MAPPED | Standalone Lean files; no roadmap articles yet. |
| Atlas/FC | MAPPED | Standalone Lean files; no roadmap articles yet. |
| Atlas/CPythonListsort | OUT | Maintained as its own Autoform blueprint inside Atlas/CPythonListsort. |
