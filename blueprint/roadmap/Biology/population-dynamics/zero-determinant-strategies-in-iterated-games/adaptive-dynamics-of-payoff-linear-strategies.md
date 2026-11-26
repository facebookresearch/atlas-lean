# Adaptive dynamics of payoff-linear strategies

**Setting.** In the infinitely repeated prisoner's dilemma with payoffs $T > R > P > S$ and $2R > T + S$, call a memory-one strategy an $(l, s)$-strategy if, against every co-player, it enforces the linear payoff relation

$$\pi_{\text{co-player}} - l = s\,(\pi_{\text{own}} - l),$$

with *baseline payoff* $l$ (the payoff it earns against itself) and *slope* $s \in [-1, 1]$; zero-determinant strategies with $s \ne 1$, unconditional defection and unconditional cooperation are of this form. Extortioners are the strategies with $l = P$ and $0 < s < 1$ (slope $s = 1/\chi$ for extortion factor $\chi$), compliers those with $l = R$ and $0 < s < 1$, and equalizers those with $s = 0$.

**Payoffs.** If player 1 uses an $(l_1, s_1)$-strategy and player 2 an $(l_2, s_2)$-strategy with $s_1 s_2 \ne 1$, the two enforced relations determine the payoffs uniquely:

$$\pi_1 = \frac{s_2(1 - s_1)\, l_1 + (1 - s_2)\, l_2}{1 - s_1 s_2}, \qquad \pi_2 = \frac{s_1(1 - s_2)\, l_2 + (1 - s_1)\, l_1}{1 - s_1 s_2}.$$

In particular two players with the same baseline $l$ both earn $l$, whatever their slopes.

**Theorem (adaptive dynamics).** In an infinite population with resident $(l, s)$, the selection gradient gives

$$\dot s = 0, \qquad \dot l = \frac{s}{1 + s}.$$

In a finite population of size $N \ge 2$ under rare mutation and weak selection, steering by fixation probability instead of invasion fitness gives $\dot s = 0$ and

$$\dot l \propto \frac{(N-1)\,s - 1}{1 + s}.$$

Hence the slope is conserved; for $N \to \infty$ populations with $s > 0$ climb to the edge of compliers ($l = R$) and those with $s < 0$ descend toward unconditional defection; for finite $N$ the baseline rises exactly when $s > 1/(N-1)$, so for $N = 2$ every interior trajectory falls, and an extortioner is stable only if $s < 1/(N-1)$, i.e. $\chi > N - 1$.

## Depends on

- [Zero-determinant strategies](zero-determinant-linear-relation.md)

## Proof depends on

- [The one-third rule for weak selection in the Moran process](../../population-genetics/moran-model/one-third-rule-under-weak-selection.md)

## Proof sketch

The payoff formula solves the linear system $\pi_2 - l_1 = s_1(\pi_1 - l_1)$, $\pi_1 - l_2 = s_2(\pi_2 - l_2)$. A rare mutant $(l', s')$ in an $(l, s)$ population earns $\pi(l', s'; l, s)$; its derivative in $s'$ vanishes at $l' = l$, and its derivative in $l'$ there is $s(1-s)/(1-s^2) = s/(1+s)$, giving the infinite-population dynamics. For finite $N$ the fixation-probability gradient is the gradient of $(N-2)\,a + (2N-1)\,b - (N+1)\,c - (2N-4)\,d$ with $a, b, c, d$ the mutant–mutant, mutant–resident, resident–mutant and resident–resident payoffs (the effective payoff matrix that removes self-interaction); differentiating in $l'$ gives $(N-2) + (2N-1)\tfrac{s}{1+s} - (N+1)\tfrac{1}{1+s} = \frac{3((N-1)s - 1)}{1+s}$. Extortioners act as catalysts: a defecting population can be left only by neutral drift along $l = P$ to a positive slope, after which cooperation is selected; removing extortioners from the mutant space lowers the long-run average payoff at every population size.

## Sources

- C. Hilbe, M. A. Nowak and A. Traulsen, "Adaptive dynamics of extortion and compliance", PLoS ONE 8 (2013), e77886, Results ("Adaptive dynamics in infinite populations", "Adaptive dynamics in finite populations", Eqs. (5)–(11)) and Methods, <https://doi.org/10.1371/journal.pone.0077886>, PMCID PMC3815207.
