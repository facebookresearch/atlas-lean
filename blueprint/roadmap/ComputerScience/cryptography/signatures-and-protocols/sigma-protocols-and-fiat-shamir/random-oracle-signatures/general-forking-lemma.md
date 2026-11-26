# The general forking lemma

Let $q \ge 1$, let $H$ be a finite set with $|H| \ge 2$, and let $\mathcal{A}$ be a randomized algorithm that on input $x$ and $h_1, \dots, h_q \in H$ returns a pair $(J, \sigma)$ with $J \in \{0, 1, \dots, q\}$, where $J = 0$ means failure. Let $\mathrm{acc}$ be the probability that $J \ge 1$ when $x$ is drawn from some input distribution, the coins $\rho$ of $\mathcal{A}$ are uniform and $h_1, \dots, h_q$ are uniform. The *forking algorithm* runs $\mathcal{A}(x, h_1,\dots,h_q; \rho)$ to obtain $(J, \sigma)$, then draws fresh $h'_J, \dots, h'_q$ and reruns $\mathcal{A}(x, h_1, \dots, h_{J-1}, h'_J, \dots, h'_q; \rho)$ to obtain $(J', \sigma')$; it succeeds if $J = J' \ge 1$ and $h_J \ne h'_J$. Its success probability $\mathrm{frk}$ satisfies

$$
\mathrm{frk} \;\ge\; \mathrm{acc}\left(\frac{\mathrm{acc}}{q} - \frac{1}{|H|}\right).
$$

## Proof sketch

Condition on $x$, $\rho$ and the prefix $h_1, \dots, h_{J-1}$; for each index $j$, the probability that both runs return $j$ is at least the square of the single-run probability by Jensen's inequality, and summing over $j$ with Cauchy–Schwarz gives $\mathrm{acc}^2/q$. Subtract the probability $\mathrm{acc}/|H|$ that the fresh answer repeats.

## Proof depends on

- [The rewinding lemma](../../zero-knowledge-and-arguments/the-rewinding-lemma.md)

## Sources

- Mihir Bellare and Gregory Neven, "Multi-Signatures in the Plain Public-Key Model and a General Forking Lemma", Proceedings of the 13th ACM Conference on Computer and Communications Security, 2006.
- David Pointcheval and Jacques Stern, "Security Arguments for Digital Signatures and Blind Signatures", Journal of Cryptology, 2000.
