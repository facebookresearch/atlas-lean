# The coriaceous theorem: the strong g-leakage order is composition refinement

**Theorem.** For all channel matrices $A$ and $B$ with the same input set, if $A \le_G B$ then $A \sqsubseteq_\circ B$. Together with the converse
[data-processing inequality](composition-refinement-implies-the-g-leakage-order.md), $V_g(\pi, A) \le V_g(\pi, B)$ for every prior $\pi$ and every gain function $g$ if and only if
$A = BR$ for some channel $R$.

If no channel $R$ gives $A = BR$, the matrix $A$ lies outside the closed convex set $\{BR\}$, and a [hyperplane strictly separating](../../../Analysis/banach-spaces/duality-and-weak-topologies/hahn-banach-theorem/strict-separation-of-a-point-from-a-closed-convex-set.md) $A$ from it yields a gain function $g$ with values in $[0, 1]$
for which $V_g(\pi_u, A) > V_g(\pi_u, B)$ under the uniform prior $\pi_u$.

## Depends on

- [Composition refinement of channels](composition-refinement-of-channels.md)

## Proof depends on

- [Composition refinement implies the strong g-leakage order](composition-refinement-implies-the-g-leakage-order.md)
- [Strict separation of a point from a closed convex set](../../../Analysis/banach-spaces/duality-and-weak-topologies/hahn-banach-theorem/strict-separation-of-a-point-from-a-closed-convex-set.md)

## Sources

- A. McIver, C. Morgan, G. Smith, B. Espinoza and L. Meinicke, "Abstract channels and their robust information-leakage ordering", *Principles of Security and Trust (POST 2014)*, LNCS 8414, Springer, 2014, pp. 83–102, copy at <https://trustworthy.systems/publications/nicta_full_text/7522.pdf>: Section 6, Theorem 9 and its proof (resolving the conjecture left open in Alvim et al., CSF 2012, Section VI).
