# Mean-square end-to-end distance of the worm-like chain

Model a semiflexible polymer of contour length $L_c > 0$ as a curve $r(s)$, $0 \le s \le L_c$, with a jointly measurable random unit tangent field $u(s) = r'(s)$ whose correlations decay with persistence length $L_p > 0$: $E[u(s) \cdot u(s')] = e^{-|s - s'|/L_p}$ (the Kratky–Porod worm-like chain). The end-to-end vector $R = \int_0^{L_c} u(s)\, ds$ then satisfies

$$E[R^2] = \int_0^{L_c}\!\!\int_0^{L_c} e^{-|s - s'|/L_p}\, ds\, ds' = 2 L_p L_c - 2 L_p^2 \bigl(1 - e^{-L_c/L_p}\bigr),$$

so $E[R^2]/L_c^2 \to 1$ as $L_c/L_p \to 0$ (rigid rod) and $E[R^2]/(2 L_p L_c) \to 1$ as $L_c/L_p \to \infty$ (flexible coil) (Kratky and Porod 1949; Rubinstein and Colby 2003, Ch. 2).

## Proof depends on

- [Fubini's theorem for iterated integrals](../../../MeasureTheory/integration/iterated-integrals/integral-integral-swap.md)

## Expansion

1. The model: a random curve with a jointly measurable unit tangent field and the stated tangent correlation; boundedness of $u$ gives the domination needed for Fubini's theorem.
2. The identity $E[R^2] = \iint E[u(s)\cdot u(s')]\, ds\, ds'$ and the evaluation of the double integral.
3. The two limits in $L_c/L_p$.

Context outside this node: a discrete freely rotating chain with bond length $b$ and adjacent tangent correlation $c_b$ approaches this model when $b \to 0$ with $c_b = e^{-b/L_p} \to 1$, so the bond angle must shrink with $b$; a fixed bond angle gives $L_p \to 0$.

## Sources

- Original model: O. Kratky and G. Porod, Röntgenuntersuchung gelöster Fadenmoleküle, Recl. Trav. Chim. Pays-Bas 68 (1949), 1106–1122. <https://doi.org/10.1002/recl.19490681203>
- M. Rubinstein and R. H. Colby, *Polymer Physics*, Oxford University Press, 2003, Ch. 2 (worm-like chain).
