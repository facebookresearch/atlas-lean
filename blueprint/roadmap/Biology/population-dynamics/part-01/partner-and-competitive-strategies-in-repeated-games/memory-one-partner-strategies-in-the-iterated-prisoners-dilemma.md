# Memory-one partner strategies in the iterated prisoner's dilemma

**Setting.** In each round of a repeated game two players choose $C$ or $D$; payoffs to player I are
$R$ (mutual cooperation), $S$ (sucker), $T$ (temptation), $P$ (mutual defection), with
$T > R > P > S$ and $2R > T + S$. With continuation probability (discount factor) $\delta < 1$, the
expected payoffs are $\pi_I = g_I \cdot v$, $\pi_{II} = g_{II} \cdot v$, where $g_I = (R, S, T, P)$,
$g_{II} = (R, T, S, P)$ and $v = (1 - \delta) \sum_{t \ge 0} \delta^t v(t)$ is the discounted mean
distribution over the outcomes $(CC, CD, DC, DD)$. A **memory-one strategy**
$p = (p_{CC}, p_{CD}, p_{DC}, p_{DD}; p_0)$ cooperates first with probability $p_0$ and afterwards with a
probability depending only on the previous outcome. A strategy is **nice** if it is never the first to
defect ($p_0 = p_{CC} = 1$ for memory-one).

**Lemma (memory-one identity).** If player I uses $p$ and player II uses any strategy, then with
$\tilde{p} = (p_{CC}, p_{CD}, p_{DC}, p_{DD})$ and $g_0 = (1, 1, 0, 0)$,

$$(\delta \tilde{p} - g_0) \cdot v = -(1 - \delta) p_0 ;$$

without discounting, $(\tilde{p} - g_0) \cdot v = 0$ whenever the limiting mean distribution exists.

**Definition.** A **partner strategy** is a nice strategy such that, whatever the co-player does,
$\pi_I < R \Rightarrow \pi_{II} < R$. A partner strategy is a Nash equilibrium against itself, and every
best reply to it yields both players exactly $R$.

**Proposition.** For a nice memory-one strategy $p$ the following are equivalent:

1. $p$ is a partner strategy;
2. against AllD $= (0, 0, 0, 0; 0)$ and against $(0, 1, 1, 1; 0)$ the co-player earns less than $R$;
3. $B_1 < 0$ and $B_2 < 0$, with $B_1$ and $B_2$ defined below.

Here

$$B_1 = \delta (T - R) p_{DD} - \delta (R - P)(1 - p_{CD}) + (1 - \delta)(T - R),$$

$$B_2 = \delta (T - R) p_{DC} - \delta (R - S)(1 - p_{CD}) + (1 - \delta)(T - R).$$

**Corollary.** A memory-one partner strategy exists if and only if Grim $= (1, 0, 0, 0; 1)$ is one, that
is, if and only if $\delta > \frac{T - R}{T - P}$. Tit-for-Tat is a partner strategy if and only if
$\delta > \frac{T - R}{T - P}$ and $\delta > \frac{T - R}{R - S}$; win-stay lose-shift if and only if
$\delta > \frac{T - R}{R - P}$ and $\delta > \frac{T - R}{T - S}$.

## Depends on

- [Is Strategy](../../zero-determinant-strategies-in-iterated-games/is-strategy.md)

## Proof depends on

- [Press–Dyson determinant lemma](../../zero-determinant-strategies-in-iterated-games/dot-product-eq-div-pd-det.md)

## Expansion

The lemma telescopes the probability that player I cooperates: $\delta q_I(t+1) - q_I(t) =
(\delta \tilde{p} - g_0) \cdot v(t)$, and the discounted sum of the left side is $-(1 - \delta) p_0$. For a
nice $p$, this identity and $\mathbf{1} \cdot v = 1$ express $v_{CD}$ through $v_{DC}$ and $v_{DD}$, and
then $\pi_{II} \ge R$ becomes $B_2 v_{DC} + B_1 v_{DD} \ge 0$. Negative $B_1, B_2$ force
$v_{DC} = v_{DD} = v_{CD} = 0$, so $\pi_I = \pi_{II} = R$. The two test strategies realize the extreme
directions $v_{DD}$ and $v_{DC}$, which is why checking them suffices; both $B_i$ are minimized by
$p_{CD} = p_{DC} = p_{DD} = 0$, so the unforgiving trigger strategy is the most effective enforcer of
cooperation among memory-one strategies. The same identity underlies the Press-Dyson
zero-determinant strategies.

## Sources

- C. Hilbe, A. Traulsen, K. Sigmund, "Partners or rivals? Strategies for the iterated prisoner's
  dilemma", Games and Economic Behavior 92 (2015), Lemmas 1-2, Definition 3, Proposition 1 and
  Corollary 1, <https://doi.org/10.1016/j.geb.2015.05.005> (PMC4547490).
