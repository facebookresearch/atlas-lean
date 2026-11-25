# Direct check of the root condition

Given code-level transition functions $s$ on codes
$\alpha$ and $t$ on codes $\beta$, each listing labelled steps to codes, a relation $R$ given as
a list of code pairs, and codes $x$ and $y$, the root check succeeds exactly when every listed
step $(a, x')$ of $s(x)$ is matched by some listed step $(a, y')$ of $t(y)$ with the same label
and $(x', y') \in R$, and every listed step $(a, y')$ of $t(y)$ is matched by some listed step
$(a, x')$ of $s(x)$ with the same label and $(x', y') \in R$.

This is a sufficient check of the root condition of observation congruence at $(x, y)$. Rooted
weak bisimilarity also allows silent steps around the matching step, so the check is incomplete.
