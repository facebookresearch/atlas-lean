# Schoen's subexponential upper bound for $W(3, k)$

Write $W(3, k)$ for the van der Waerden
number: the least $n$ such that every red/blue colouring of $\{1, \dots, n\}$ has a red $3$-term
or a blue $k$-term arithmetic progression (progressions have common difference $d > 0$). Say that
$N$ forces $W(3, k)$ if every red/blue colouring of $\{1, \dots, N\}$ has a red $3$-term or a
blue $k$-term arithmetic progression. There is a real constant $c < 1$ such that for all
sufficiently large natural numbers $k$ some natural number $N < \exp(k^c)$ forces $W(3, k)$.
Equivalently, $W(3, k) < \exp(k^c)$ for all large $k$.

Schoen proved $W(3, k) \le \exp(O(k^{1-\delta}))$ for an absolute constant $\delta > 0$, which gives
this statement; erdosproblems.com/721 records Schoen as the first to show it. The best known bound
is now $\exp(O((\log k)^9))$, via Bloom and Sisask.

## Sources

- T. F. Bloom, Erdős Problems, Problem #721, https://www.erdosproblems.com/721 (status SOLVED); resolution: T. Schoen, A subexponential upper bound for van der Waerden numbers W(3, k), Electron. J. Combin. 28 (2021), Paper 2.34; B. Green, New lower bounds for van der Waerden numbers, Forum Math. Pi 10 (2022), e18, Schoen's abstract: N ≤ exp(O(k^{1-c})) for an absolute c > 0 whenever {1, …, N} splits into a 3-AP-free part and a k-AP-free part; abstract of arXiv:2102.01543 (Green): w(3, k) ≥ k^{b(k)} with b(k) = c (log k / log log k)^{1/3}; erdosproblems.com/721: both specific challenges of Erdős have been met, https://www.combinatorics.org/ojs/index.php/eljc/article/view/v28i2p34.
