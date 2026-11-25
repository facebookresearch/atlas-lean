# Closed-loop transfer maps of a feedback loop

Let $G(s) = C(sI - A)^{-1}B + D \in \mathbb{C}^{p \times m}$ be the transfer matrix of a plant and $K(s) = C_K(sI - A_K)^{-1}B_K + D_K \in \mathbb{C}^{m \times p}$ that of a controller. Close the loop with unit negative feedback: the error is $e = r - y$, the controller output is $u = K e$, and the plant output is $y = G u$. Fix $s \in \mathbb{C}$ outside the spectra of $A$ and $A_K$, so that $G(s)$ and $K(s)$ are defined, and suppose $I_p + G(s) K(s)$ is invertible. Then for every reference value $r \in \mathbb{C}^p$ the loop equations have exactly one solution, given by

$$e = S\, r, \qquad y = T\, r, \qquad u = K S\, r,$$

where

$$S = (I_p + GK)^{-1}, \qquad T = GK\, (I_p + GK)^{-1} = (I_p + GK)^{-1}\, GK,$$

all evaluated at $s$. These are the sensitivity $S$ and the complementary sensitivity $T$, and they satisfy $S + T = I_p$.

The loop equations give $e = r - GKe$, that is, $(I_p + GK)e = r$, so $e$ is unique and equals $Sr$; then $u = Ke$ and $y = GKe$. The two forms of $T$ agree because $GK$ commutes with $I_p + GK$, hence with its inverse. Finally $S + T = (I_p + GK)^{-1}(I_p + GK) = I_p$. Invertibility of $I_p + GK$ is equivalent to invertibility of $I_m + KG$, by $\det(I_p + GK) = \det(I_m + KG)$, and then $K(I_p + GK)^{-1} = (I_m + KG)^{-1}K$.

In the single-input single-output case, with process $P = G$ and controller $C = K$, these are the source's $S = 1/(1 + PC)$, $T = PC/(1 + PC)$ and $CS = C/(1 + PC)$.

## Background

- [Controller-form realization of a proper rational transfer matrix](../realization-theory/controller-form-realization-of-a-proper-rational-transfer-matrix.md): transfer matrices $C(sI - A)^{-1}B + D$ of state-space systems
- [Laplace transform of the matrix exponential and of the state of a linear system](../realization-theory/laplace-transform-of-the-state-of-a-linear-system.md): the transfer matrix as the ratio of output and input Laplace transforms

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021 (electronic edition v3.0i, <http://fbsbook.org>), Section 12.1, the Gang of Four sensitivity functions (12.2) with $S = 1/(1 + PC)$, $T = PC/(1 + PC)$, $CS = C/(1 + PC)$ and Table 12.1 (pp. 12-2–12-3).
