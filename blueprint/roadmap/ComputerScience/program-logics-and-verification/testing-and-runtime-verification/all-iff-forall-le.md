# Bounded-exhaustive checking is exact under exact support

Let $\mathit{enum} : \mathbb{N} \to \mathrm{List}\,\alpha$ be an enumerator, $\mathit{size} : \alpha \to \mathbb{N}$, $p : \alpha \to \mathrm{Bool}$ and $n \in \mathbb{N}$. If the enumeration at bound $n$ has exact support, $x \in \mathit{enum}(n) \iff \mathit{size}(x) \le n$ for all $x$, then $p$ holds on every element of the list $\mathit{enum}(n)$ if and only if $p(x) = \mathrm{true}$ for every $x$ with $\mathit{size}(x) \le n$.

When the enumerator is only complete at $n$, passing the check still implies validity up to $n$ ([Passing a bounded check implies bounded validity](forall-le-of-all.md)), but the converse can fail when the enumerator also lists larger inputs. A passing bounded check says nothing about inputs above the bound. To test $p$ on a subset of inputs, apply these statements to the subtype of inputs satisfying the restricting predicate, with an enumerator of that subtype.

## Sources

- K. Claessen and J. Hughes, "QuickCheck: a lightweight tool for random testing of Haskell programs", *Proceedings of ICFP 2000*, ACM, 2000: property-based testing context only; these statements are deterministic, while QuickCheck uses random generators.
