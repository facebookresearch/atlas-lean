# Amplitude amplification

Let $\mathcal{A}$ be a unitary quantum algorithm (no intermediate measurements) on a space with a good subspace given by a
projector $\Pi$, and let $p = \lVert \Pi \mathcal{A} \lvert 0 \rangle \rVert^2 \in (0, 1]$. Amplitude amplification
applies $(-\mathcal{A} S_0 \mathcal{A}^{-1} S_\Pi)^j \mathcal{A}$, where $S_\Pi$ and $S_0$ are the phase reflections
$I - 2\Pi$ and $I - 2\lvert 0 \rangle\langle 0 \rvert$.

1. **Known $p$.** With $\theta = \arcsin\sqrt p \in (0, \pi/2]$ and $j = \lfloor \pi/(4\theta) \rfloor$, measuring $\Pi$ on the
   final state yields a good state with probability $\sin^2((2j+1)\theta) \ge \max(1-p, p)$, using $j \le \pi/(4\sqrt p)$
   applications each of $\mathcal{A}$ and $\mathcal{A}^{-1}$ besides the first $\mathcal{A}$. If the gate model also implements exactly
   the phase-generalized reflections $I - (1 - e^{i\varphi})\Pi$ and $I - (1 - e^{i\phi})\lvert 0 \rangle\langle 0 \rvert$, or a single-qubit
   rotation that lowers the success probability to $\sin^2(\pi/(4m+2))$ with $m = \lceil \pi/(4\theta) - 1/2 \rceil$, then
   success probability $1$ is reached with $\Theta(1/\sqrt p)$ applications of $\mathcal{A}$ and $\mathcal{A}^{-1}$; this exact variant
   depends on that gate model.
2. **Unknown $p$.** The randomized schedule that, in round $l = 1, 2, \dots$, first measures $\mathcal{A} \lvert 0 \rangle$ once and
   then measures $(-\mathcal{A} S_0 \mathcal{A}^{-1} S_\Pi)^{j} \mathcal{A} \lvert 0 \rangle$ for $j$ uniform in $\{1, \dots, \lceil c^l \rceil\}$, with a fixed
   $1 < c < 2$, and stops at the first good outcome, finds a good state using an expected $\Theta(1/\sqrt p)$ applications of
   $\mathcal{A}$ and $\mathcal{A}^{-1}$, as a separate statement.

## Expansion

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Measurements (POVM, projective) and the Born rule.

## Depends on

- [Unitary evolution and elementary gates](../../QuantumInformation/quantum-foundations/unitary-evolution-and-elementary-gates.md)

## Related topics

- [Symmetric amplitude vector](grover-s-algorithm/symmetric-amplitude.md)

## Sources

- G. Brassard, P. Høyer, M. Mosca and A. Tapp, "Quantum amplitude amplification and estimation", arXiv:quant-ph/0005055, equation (1), equation (8), Theorem 2 (known $a$, $m = \lfloor \pi/4\theta_a \rfloor$, success at least $\max(1-a, a)$), Theorem 3 (QSearch) and Theorem 4 with Section 2.1 (success with certainty). <https://arxiv.org/abs/quant-ph/0005055>
- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §7.3 (the same procedure, with $\pi/(4\theta) - 1/2$ rounded to the nearest integer). <https://arxiv.org/pdf/1907.09415v6>
