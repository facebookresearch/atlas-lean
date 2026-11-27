# Restriction Algebra

The proposition that restriction of sections of tensor powers is multiplicative: for a morphism
$f : Y \to X$ of $k$-schemes, a line bundle $L$ on $X$ with section products `A` (`SectionProduct`:
maps $L^{\otimes a} \otimes L^{\otimes b} \to L^{\otimes (a + b)}$ normalized on local powers),
section products `B` on $f^*L$, comparisons $f^*(L^{\otimes m}) \cong (f^*L)^{\otimes m}$ (`P`) and
the restriction maps $R_m : H^0(X, L^{\otimes m}) \to H^0(Y, (f^*L)^{\otimes m})$ given by pullback
followed by the comparison (`PowerRestriction`), $R_{a+b}(s \cdot t) = R_a(s) \cdot R_b(t)$ for all
$a, b$ and all global sections $s$ of $L^{\otimes a}$ and $t$ of $L^{\otimes b}$, the products
being those of `A` and `B`.
