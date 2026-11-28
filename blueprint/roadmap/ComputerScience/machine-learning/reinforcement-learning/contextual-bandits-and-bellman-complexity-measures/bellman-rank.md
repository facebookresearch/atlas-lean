# Contextual decision processes and Bellman rank

A **contextual decision process** is an episodic process of horizon $H$ with rich observations $x_h$, actions from a finite set of size $K$ and rewards, where the dynamics may depend on unobserved state. Given a class $\mathcal{F}$ of value functions $f = (f_1, \dots, f_H)$, $f_h : \mathcal{X} \times \mathcal{A} \to [0,1]$ (with greedy policies $\pi_f$), the **average Bellman error** of $f$ at level $h$ under the roll-in policy $\pi_{f'}$ is

$$
\mathcal{E}_h(f', f) = \mathbb{E}_{\pi_{f'}}\big[ f_h(x_h, a_h) - r_h - f_{h+1}(x_{h+1}, \pi_f(x_{h+1})) \big],
$$

with $a_h = \pi_f(x_h)$ and the convention $f_{H+1} \equiv 0$, so that at the last level $\mathcal{E}_H(f', f) = \mathbb{E}_{\pi_{f'}}\big[f_H(x_H, a_H) - r_H\big]$. The **Bellman rank** is the smallest $M$ such that for every $h$ the matrix $[\mathcal{E}_h(f', f)]_{f', f \in \mathcal{F}}$ factorizes as $\langle \nu_h(f'), \xi_h(f)\rangle$ with $\nu_h(f'), \xi_h(f) \in \mathbb{R}^M$ and $\|\nu_h(f')\|_2\, \|\xi_h(f)\|_2 \le \zeta$ for a norm parameter $\zeta < \infty$; rewards satisfy $r_h \ge 0$ and $\sum_h r_h \le 1$. Tabular MDPs, reactive POMDPs and linear models of the transition operator have small Bellman rank.

## Depends on

- [Stochastic policy](../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)

## Sources

- N. Jiang, A. Krishnamurthy, A. Agarwal, J. Langford, R. E. Schapire, "Contextual Decision Processes with Low Bellman Rank are PAC-Learnable", ICML (2017), arXiv:1610.09512, Definitions 1, 2 and 5 and Assumption 1.
