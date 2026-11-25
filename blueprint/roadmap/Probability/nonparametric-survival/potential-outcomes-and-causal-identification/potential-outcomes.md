# Potential-outcomes model with binary instrument and treatment

Let $\Omega$ be a measurable space. A potential-outcomes model on $\Omega$ consists of measurable functions $Z : \Omega \to \{0, 1\}$ (the assigned instrument), $D(z) : \Omega \to \{0, 1\}$ for $z \in \{0, 1\}$ (the potential treatments) and $Y(z, d) : \Omega \to \mathbb{R}$ for $z, d \in \{0, 1\}$ (the potential outcomes). The observed treatment is $D(Z)$ and the observed outcome is $Y(Z, D(Z))$. The identifying assumptions ([independence](independence.md), [exclusion](exclusion.md), [monotonicity](monotonicity.md), relevance) are separate hypotheses (Imbens & Angrist 1994; Angrist, Imbens & Rubin 1996).

## Sources

- G. W. Imbens, J. D. Angrist, *Identification and estimation of local average treatment effects*, Econometrica 62 (1994), 467–475.
- J. D. Angrist, G. W. Imbens, D. B. Rubin, *Identification of causal effects using instrumental variables*, J. Amer. Statist. Assoc. 91 (1996), 444–455.
