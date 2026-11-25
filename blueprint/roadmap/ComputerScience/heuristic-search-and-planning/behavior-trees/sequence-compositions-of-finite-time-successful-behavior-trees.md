# Sequence compositions of finite-time-successful behavior trees

Let $T_1$ and $T_2$ be behavior trees on the same state space, finite time successful with regions of attraction $\mathcal{R}'_1$, $\mathcal{R}'_2$ and time bounds $\tau_1$, $\tau_2$, and suppose that the success region of the first child is exactly what the second child needs: $\mathcal{S}_1 = \mathcal{R}'_2 \cup \mathcal{S}_2$. Then $T_0 = \mathrm{Sequence}(T_1, T_2)$ is finite time successful with region of attraction $\mathcal{R}'_1 \cup \mathcal{R}'_2$, success region $\mathcal{S}_0 = \mathcal{S}_1 \cap \mathcal{S}_2 = \mathcal{S}_2$ and time bound $\tau_1 + \tau_2$.

The hypothesis $\mathcal{S}_1 = \mathcal{R}'_2 \cup \mathcal{S}_2$ says that the second action never undoes the first: while $T_2$ runs, the state stays in $\mathcal{R}'_2 \cup \mathcal{S}_2 = \mathcal{S}_1$, so the sequence keeps executing $T_2$ rather than returning to $T_1$.

**Proof.** If $x(0) \in \mathcal{R}'_1$, then $x(0) \notin \mathcal{S}_1$, so the sequence executes $f_1$, and since $T_1$ is finite time successful the state stays in $\mathcal{R}'_1$ and enters $\mathcal{S}_1$ within $\tau_1$ steps. If the state is in $\mathcal{S}_1 = \mathcal{R}'_2 \cup \mathcal{S}_2$ and not yet in $\mathcal{S}_2$, it is in $\mathcal{R}'_2$; the sequence executes $f_2$, and $T_2$ keeps the state in $\mathcal{R}'_2 \subseteq \mathcal{S}_1$ until it enters $\mathcal{S}_2$ within $\tau_2$ further steps, where the sequence returns $r_2 = S$. Starting in $\mathcal{R}'_2$ only the second phase occurs. Since $\mathcal{S}_2 \subseteq \mathcal{S}_1$, the sequence succeeds exactly on $\mathcal{S}_2$.

## Depends on

- [Behavior trees as switched difference equations](behavior-trees-as-switched-difference-equations.md): sequence compositions and finite time success

## Sources

- M. Colledanchise and P. Ögren, *Behavior Trees in Robotics and AI: An Introduction*, CRC Press, 2018, <https://arxiv.org/abs/1709.00084>, Lemma 5.2 (robustness and efficiency of sequence compositions: if $T_1$, $T_2$ are finite time successful with $S_1 = R'_2 \cup S_2$, then $\mathrm{Sequence}(T_1, T_2)$ is finite time successful with $\tau_0 = \tau_1 + \tau_2$, $R'_0 = R'_1 \cup R'_2$ and $S_0 = S_1 \cap S_2 = S_2$, p. 67) and Example 5.1. The proof is written out on the page.
