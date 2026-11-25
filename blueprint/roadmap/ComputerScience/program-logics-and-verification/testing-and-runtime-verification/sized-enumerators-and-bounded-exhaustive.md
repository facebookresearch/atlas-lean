# Sized enumerators and bounded exhaustive property testing

Let $\mathrm{size}$ be a size function on a type of test inputs, $\mathrm{enum}$ a sized enumerator assigning to each bound $n$ a
finite list $\mathrm{enum}(n)$ of inputs, and $p$ a Boolean property of inputs. Fix a bound $n$.

- If $\mathrm{enum}$ has exact support at $n$, that is, $x \in \mathrm{enum}(n)$ exactly when $\mathrm{size}(x) \le n$, then $p$ holds for every
  element of $\mathrm{enum}(n)$ if and only if $p$ holds for every input $x$ with $\mathrm{size}(x) \le n$.
- If $\mathrm{enum}$ is only complete at $n$, that is, every $x$ with $\mathrm{size}(x) \le n$ occurs in $\mathrm{enum}(n)$, then $p$ holding for every
  element of $\mathrm{enum}(n)$ still implies that $p$ holds for every input of size at most $n$; the converse can fail when the
  enumerator also lists larger inputs.

A passing bounded check says nothing about inputs above the bound. To test $p$ on a subset of inputs, apply these
statements to the subtype of inputs satisfying the restricting predicate, with an enumerator of that subtype.

## Sources

- K. Claessen and J. Hughes, "QuickCheck: a lightweight tool for random testing of Haskell programs", *Proceedings of ICFP 2000*, ACM, 2000: property-based testing context only; the bounded exhaustive statements here are deterministic, not claims about random generators.
