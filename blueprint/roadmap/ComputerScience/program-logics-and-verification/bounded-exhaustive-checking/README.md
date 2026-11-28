# Bounded-exhaustive checking

For a size function on test inputs, a sized enumerator listing a finite list of inputs for each bound $n$, and a Boolean property $p$, the pages below relate a passing bounded check to validity up to the bound. When the enumerator is only complete at $n$, passing the check still implies validity up to $n$, but the converse can fail when the enumerator also lists larger inputs. A passing bounded check says nothing about inputs above the bound. To test $p$ on a subset of inputs, apply these statements to the subtype of inputs satisfying the restricting predicate, with an enumerator of that subtype. These statements are deterministic; property-based testing in the sense of K. Claessen and J. Hughes, "QuickCheck: a lightweight tool for random testing of Haskell programs", *Proceedings of ICFP 2000*, ACM, 2000, uses random generators instead.

- [Bounded-exhaustive checking is exact under exact support](all-iff-forall-le.md)
- [Passing a bounded check implies bounded validity](forall-le-of-all.md)
- [Exact-support enumerations are monotone in the bound](mem-of-mem-le.md)
- [Budget-split product enumeration](enum-prod.md)
- [Membership in the budget-split product enumeration](mem-enum-prod-iff.md)
