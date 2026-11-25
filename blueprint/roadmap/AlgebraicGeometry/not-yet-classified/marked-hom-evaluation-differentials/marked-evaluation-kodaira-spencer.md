# Marked Evaluation Kodaira Spencer

The Kodaira–Spencer map of a family of maps, evaluated at a marked point, is the derivative of
the evaluation map: let $k$ be a field, $C$ a smooth proper $k$-scheme with $n$ disjoint rational
marked points, $V$ a smooth $k$-scheme, and $U$ an étale atlas of the given stack of maps $C \to V$
(`FixedModel`), with universal map $f : C \times U \to V$ and the given differential data (and
derived-functor interfaces `HasDerivedPullbacks`, `HasDerivedPushforwards`, `HasDerivedTensors`).
Then for each marking $i$, the degree-zero Kodaira–Spencer map
$T_U \to H^0(C \times U / U, f^* T_V)$ followed by restriction to the $i$-th marking, through the
given identification `Z` of $H^0$ of the derived direct image, is the derivative
$T_U \to \mathrm{ev}_i^* T_V$ of the $i$-th evaluation map $\mathrm{ev}_i : U \to V$.
