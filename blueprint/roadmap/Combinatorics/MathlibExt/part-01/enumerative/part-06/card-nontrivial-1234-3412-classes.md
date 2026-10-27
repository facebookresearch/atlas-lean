---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.card_nontrivial_1234_3412_classes
---

# Nontrivial1234 3412 Classes

For n ≥ 7, the number of nontrivial equivalence classes of S_n under the {1234,
3412}-equivalence is (n^3 + 6n^2 - 55n + 54)/6, conjectured by Ma and given by sequence A330395.

Proof: Decompose the exceptional set into swap classes and a generic part. Kernel-checked
finite certificates handle the `S₅`/`S₆` classes, `S₇` reachability, and the `S₈` deletion
boundary. Point insertion then gives the recurrence, whose solution is the displayed polynomial.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.Nontrivial1234_3412Classes](../../../../../../sources/v2/MathlibExt.md)
- Quinn Perian, Bella Xu, and Alexander Lu Zhang, "Counting the Nontrivial Equivalence Classes of Sn Under {1234,3412}-Pattern-Replacement", Journal of Integer Sequences 23 (2020), Article 20.10.2, Theorem `thm:nontrivial`, lines 172-175, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Zhang/zhang6.tex>.
