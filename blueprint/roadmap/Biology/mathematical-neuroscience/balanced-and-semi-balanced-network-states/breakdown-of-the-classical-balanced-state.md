# Breakdown of the classical balanced state

**Mean-field model.** Population-averaged rates $r \in \mathbb R^n$ of a recurrent network obey

$$\tau \dot r = -r + f\big(\overline{JK}\,[W r + X]\big),$$

where $f$ is a non-decreasing f–I curve, $W = (w_{ab})$ the effective connectivity with $w_{ab} = J_{ab}K_{ab}/\overline{JK}$ ($K_{ab}$ the mean number and $J_{ab}$ the mean strength of connections from population $b$ to $a$), $\overline{JK} = \operatorname{mean}_{a,b}|J_{ab}|K_{ab}$ the coupling strength, and $X = W_x r_x$ the external input. The total input is $I = \overline{JK}\,[Wr + X]$.

**Classical balanced state.** If $I = O(1)$ while $\overline{JK} \to \infty$, then $Wr + X = O(1/\overline{JK})$, and in the limit

$$r = -W^{-1} X,$$

a linear function of the stimulus; balanced network theory requires this predicted $r$ to be non-negative.

**Theorem.** Let $W$ be a real non-singular $n \times n$ matrix satisfying Dale's law (each column is entrywise non-negative or entrywise non-positive), with every column non-zero and at least one positive entry. Then there exists $X$ with all entries strictly positive (a purely excitatory stimulus) for which $r = -W^{-1}X$ has a negative entry. In fact there are infinitely many such $X$.

## Expansion

Order the populations so that the non-negative (excitatory) columns of $W$ come first. Choose $v$ with strictly negative entries at the excitatory indices and strictly positive entries at the inhibitory indices, and set $X = -Wv$. Each row of $X$ is $-\sum_b w_{ab} v_b$, a sum of non-negative terms ($w_{ab} \ge 0$ with $v_b < 0$, or $w_{ab} \le 0$ with $v_b > 0$), and it is strictly positive because every column of $W$ has a non-zero entry and at least one row receives a non-zero contribution; then $r = -W^{-1}X = v$ has negative entries at every excitatory population. Every choice of such $v$ gives a different $X$. Hence any Dale's-law architecture has stimuli that break the classical balanced state, and in networks with many populations the region of stimulus space where $-W^{-1}X \ge 0$ shrinks quickly.

## Sources

- C. Baker, V. Zhu, R. Rosenbaum, "Nonlinear stimulus representations in neural circuits with approximate excitatory-inhibitory balance", PLoS Computational Biology 16 (2020) e1008192, Results (rate model, Eq. 1; total input, Eq. 2; balanced rates, Eq. 3) and Methods (Theorem 1 with proof), <https://doi.org/10.1371/journal.pcbi.1008192> (PMC7526938).
