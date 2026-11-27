# Narrow efficiency window for costly punishment

Keep the donation game with reputations, with benefit $b$, cost $c$, punishment cost $\alpha$ to the donor, punishment damage $\beta$ to the recipient, and social resolution $q$, and the three action rules $CD$, $CP$, $DD$ of the [stability analysis](evolutionary-stability-of-cooperative-action-rules.md). Call a rule **efficient** when it is evolutionarily stable and attains the highest average payoff at equilibrium among the stable rules.

**Classification.**

1. If $q > c/b$, then $CD$ is efficient.
2. If $c/b > q > c/(b + \beta)$, then $CP$ is evolutionarily stable if and only if in addition $q > \alpha/(b + \beta)$ (automatic when $\alpha \le c$), and $CP$ is both stable and more efficient than $DD$ if and only if both inequalities hold:

$$q > \frac{\alpha}{b + \beta} \qquad\text{and}\qquad q > \frac{\alpha + \beta - b + c}{\alpha + \beta + b - c};$$

otherwise $DD$ is more efficient than $CP$. If $b < c$, then $DD$ is always more efficient than $CP$.
3. If $c/(b + \beta) > q$, then $DD$ is the only evolutionarily stable rule.

So whenever cooperation sustained by withholding help is stable at all, it beats cooperation sustained by punishment; punishment is the efficient equilibrium only in the intermediate band $c/(b+\beta) < q < c/b$, and only when the two displayed inequalities also hold. The band is easily empty. With $b = 2$, $c = 1$, $\alpha = 1/2$, $\beta = 2$, the rule $CD$ is efficient for $q > 1/2$, $CP$ for $1/2 > q > 3/7$ and $DD$ for $q < 3/7$; raising the punishment damage to $\beta \ge 5/2$ removes the $CP$ region entirely.

## Depends on

- [Evolutionary stability of cooperative action rules under indirect reciprocity](evolutionary-stability-of-cooperative-action-rules.md)

## Expansion

The reason punishment loses on payoff even when it wins on stability is that at equilibrium the punishing rule is still used: errors in reputation assignment mean a fraction of interactions involve a good donor facing a recipient wrongly labelled bad, and each such interaction burns $\alpha + \beta$ of total payoff instead of simply forgoing $b - c$. The threshold $q > \alpha/(b+\beta)$ is the requirement that this waste be small relative to the deterrent it buys, and the second inequality compares the resulting average payoff against the all-defect baseline, which costs nothing at all. The condition $b < c \Rightarrow DD$ is the degenerate case where cooperation destroys value and no reputation mechanism can help. The conclusion is directional: as a society's ability to track reputations improves, $q$ rises past $c/b$ and the efficient arrangement switches from punishment to simple withholding of help, so better information displaces costly punishment rather than reinforcing it.

## Sources

- H. Ohtsuki, Y. Iwasa and M. A. Nowak, "Indirect reciprocity provides only a narrow margin of efficiency for costly punishment", Nature 457 (2009), 79–82, main text (the three-case classification, Eq. (1), the numerical example and Fig. 3), <https://doi.org/10.1038/nature07601>, PMCID PMC2614697.
