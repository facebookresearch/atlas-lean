# De Rham Module Comparison

The de Rham comparison of prismatic cohomology, as derived modules (Bhatt–Scholze, Theorem
1.8(3)): let $p$ be a prime, $(A, I)$ a bounded prism and $X$ a $p$-adic formal scheme over $A/I$
whose levels $X_n$ are smooth, quasi-compact and quasi-separated over $A/(I + (p)^{n+1})$. Assume
that derived global sections on its prismatic site and derived base change along $A → A/I$,
$a ↦ φ(a) \bmod I$, exist (`HasDerivedSections`, `HasExtension`), and let `C` be a chosen derived
$p$-completion on $A/I$-modules and `S` a system of de Rham hypermodels of $X$. Then the
$p$-completed derived base change of the prismatic cohomology of $X$ along this map is isomorphic to
the formal de Rham complex of `S`. The base change is applied to global sections, which is why $X$
is assumed quasi-compact and quasi-separated.
