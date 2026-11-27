# Linear–logarithmic phase transition for local alignment scores

Let $A_1, A_2, \dots$ and $B_1, B_2, \dots$ be letters from a finite or countable alphabet, all independent and drawn from one common law, with $0 < P(A_1 = B_1) < 1$ (the common law of the source, p. 201; without $P(A_1 = B_1) < 1$ both strings could consist of a single repeated letter, and the phase transition below would fail). Score alignments by $+1$ per match, $-\mu$ per mismatch and $-\delta$ per deleted letter, with $(\mu, \delta) \in [0, \infty]^2$. Let $S_t$ be the optimal score of $A_1\cdots A_t$ against $B_1\cdots B_t$; since $ES_{k+l} \ge ES_k + ES_l$, the limit $a(\mu, \delta) = \lim_k ES_k/k = \sup_k ES_k/k$ exists, and $a(\infty, 0)$ is the Chvátal–Sankoff constant for longest common subsequences. Let $M_n$ be the optimal local alignment score between $A_1\cdots A_n$ and $B_1\cdots B_n$ over contiguous regions. Arratia and Waterman (1994, Theorem 1, proved by combining Lemmas 1–3) prove a phase transition between linear and logarithmic growth of $M_n$: the set $\{a(\mu, \delta) = 0\}$ is a line in $[0, \infty]^2$ separating $\{a > 0\}$ from $\{a < 0\}$ (Lemma 1); if $a(\mu, \delta) > 0$ then $M_n/n \to a(\mu, \delta)$ in probability (Lemma 3); and if $a(\mu, \delta) < 0$ then, with $r(q) = \lim_t -t^{-1}\log P(S_t \ge qt)$, which is positive for $q \ge 0$ by the large deviation result of their Section 3 (Theorem 2, via the Azuma–Hoeffding inequality; when both penalties are infinite the bounded-differences constant in their (18) is not finite, and this corner is treated directly: the global score $S_t$ is $t$ on an exact match $A_1\cdots A_t = B_1\cdots B_t$ and $-\infty$ otherwise, so $P(S_t \ge qt) = P(A_1 = B_1)^t$ for $0 \le q \le 1$ and $P(S_t \ge qt) = 0$ for $q > 1$), and $b = \max_{q \ge 0} q/r(q)$ (where $r(1) = -\log P(A_1 = B_1)$, as used in Lemma 2), the ratio $M_n/\log n$ lies between $b$ and $2b$ up to factors $1 \pm \varepsilon$ with probability tending to $1$ (Lemma 2). They conjecture that the upper bound $2b$ is sharp.

## Depends on

- [Valid alignment of two sequences](../../../Biology/bioinformatics/sequence-alignment/pairwise-sequence-alignment/is-alignment.md): the alignments scored, whose two rows recover the two sequences

## Proof depends on

- [Azuma's inequality](../../../Probability/concentration-inequalities/azuma-inequality.md)
- [Functions of disjoint blocks of independent random variables](../../../Probability/foundations/independent-events-and-random-variables/pi-systems-and-independence/independent-disjoint-blocks-functions.md): failure probabilities of local scores on disjoint blocks multiply (Arratia and Waterman 1994, p. 207)
- [Kingman's subadditive ergodic theorem (nonnegative case)](../../../Dynamics/ergodic-theory/kingman-s-subadditive-ergodic-theorem/kingman-subadditive.md): applied to $n - S_n$ in the positive phase (Lemma 3, p. 209)

## Expansion

1. The model, the scoring scheme, the global score $S_t$, and the existence of $a(\mu, \delta)$ by superadditivity of expectations (compare [Fekete's lemma for the expectations of a subadditive cocycle](../../../Dynamics/ergodic-theory/kingman-s-subadditive-ergodic-theorem/tendsto-exp-seq-div.md)).
2. Lemma 1: monotonicity of $a$ in each parameter and the inequality $a(\mu + \varepsilon, \delta + \varepsilon/2) \ge a(\mu, \delta) - \varepsilon$, giving the separating line.
3. Theorem 2: positivity of the large deviation rate $r(q)$ when $a < 0$ and $q \ge 0$, by the Azuma–Hoeffding inequality outside the corner where both penalties are infinite; in that corner, directly from $P(S_t \ge qt) = P(A_1 = B_1)^t$ for $0 \le q \le 1$ and $0$ for $q > 1$.
4. Lemma 2 (logarithmic phase, with the factor $2$ gap from independent blocks) and Lemma 3 (linear phase).
5. Unequal lengths, generalized scoring schemes (Theorem 1′ and Theorem 2′), Markov letters, and Conjectures 1–4, as separate statements.

## Sources

- R. Arratia and M. S. Waterman, A phase transition for the score in matching random sequences allowing deletions, Ann. Appl. Probab. 4 (1994), 200–225, Theorem 1, Lemmas 1–3, Theorem 2. <https://doi.org/10.1214/aoap/1177005208>
