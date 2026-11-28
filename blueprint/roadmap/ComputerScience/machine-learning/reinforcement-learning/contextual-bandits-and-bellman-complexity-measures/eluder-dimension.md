# Eluder dimension

Let $\mathcal{F}$ be a class of functions $\mathcal{A} \to \mathbb{R}$ and $\varepsilon > 0$. An action $a$ is **$\varepsilon$-dependent** on actions $a_1, \dots, a_n$ with respect to $\mathcal{F}$ if every pair $f, f' \in \mathcal{F}$ with $\sqrt{\sum_{i=1}^n (f(a_i) - f'(a_i))^2} \le \varepsilon$ also satisfies $|f(a) - f'(a)| \le \varepsilon$; it is **$\varepsilon$-independent** otherwise. The **eluder dimension** $\dim_E(\mathcal{F}, \varepsilon)$ is the length of the longest sequence of actions for which there is a single $\varepsilon' \ge \varepsilon$ such that every element is $\varepsilon'$-independent of its predecessors. For linear functions $a \mapsto \langle \phi(a), \rho\rangle$ in dimension $d$ with bounded features and parameters, $\dim_E(\mathcal{F}, \varepsilon) = O(d\log(1/\varepsilon))$.

## Sources

- D. Russo, B. Van Roy, "Learning to Optimize via Posterior Sampling", Mathematics of Operations Research 39 (2014), arXiv:1301.2609, Definitions 2 and 3 and Example 7.
- C. Jin, Q. Liu, S. Miryoosefi, "Bellman Eluder Dimension: New Rich Classes of RL Problems, and Sample-Efficient Algorithms", NeurIPS (2021), arXiv:2102.00815, Definitions 4 and 5.
