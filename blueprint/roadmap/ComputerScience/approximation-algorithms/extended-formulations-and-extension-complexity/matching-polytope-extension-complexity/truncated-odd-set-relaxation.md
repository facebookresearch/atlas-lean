# Dropping large odd-set constraints gives a (1+eps)-approximate matching relaxation

For $\varepsilon \in (0,1]$ let

$$
K_\varepsilon=\Big\{x \in \mathbb{R}_{\ge 0}^{E} : x(\delta(v)) \le 1\ \forall v,\ \ x(E(U)) \le \tfrac{|U|-1}{2}\ \ \forall U \subseteq V,\ |U|\ \text{odd},\ |U| \le 1+\tfrac1\varepsilon\Big\}.
$$

Then $K_\varepsilon$ is a $(1+\varepsilon)$-approximate relaxation of $P_{\mathrm{M}}(n)$ described by $O(n^{1+1/\varepsilon})$ inequalities.

## Proof sketch

Edmonds' theorem gives $P_{\mathrm{M}}(n) \subseteq K_\varepsilon$. For $x \in K_\varepsilon$ and an odd set $U$ with $|U| > 1+1/\varepsilon$, the degree constraints give $x(E(U)) \le |U|/2 \le (1+\varepsilon)\tfrac{|U|-1}{2}$, because $|U|/(|U|-1) \le 1+\varepsilon$ exactly when $|U| \ge 1+1/\varepsilon$. Hence $x/(1+\varepsilon)$ satisfies all of Edmonds' inequalities and lies in $P_{\mathrm{M}}(n)$.

## Depends on

- [Multiplicatively approximate relaxations of the matching polytope](approximate-polytope-relaxation.md)
- [Matching polytope](../../../../GraphTheory/matchings-and-flows/matching-polytope/matching-polytope.md)

## Proof depends on

- [Edmonds' matching polytope theorem](../../../../GraphTheory/matchings-and-flows/matching-polytope/matching-polytope-eq.md)

## Sources

- Jack Edmonds, "Maximum Matching and a Polyhedron with 0,1-Vertices", Journal of Research of the National Bureau of Standards (1965).
- Makrand Sinha, "Lower Bounds for Approximating the Matching Polytope", SODA (2018), ECCC TR17-185.
