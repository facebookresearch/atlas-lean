# Fibonacci count of parity-preserving permutations avoiding $312$ and $231$

For every
integer $n \ge 1$, the number of permutations $\pi$ of $\{0, 1, \dots, n-1\}$ such that
$\pi(i) \equiv i \pmod 2$ for every $i$ and that avoid the patterns $312$ and $231$ equals the
Fibonacci number $F_n$, where $F_1 = F_2 = 1$. Here $\pi$ contains $312$ if there are
$i < j < k$ with $\pi(j) < \pi(k) < \pi(i)$, and contains $231$ if there are $i < j < k$ with
$\pi(k) < \pi(i) < \pi(j)$.

Equivalently, these are the parity-alternating permutations of $\{1, \dots, n\}$ that start with
an odd entry and avoid $312$ and $231$.

## Sources

- Per Alexandersson, Samuel Asefa Fufa, and Frether Getachew Kebede, "Pattern-Avoidance and Fuss–Catalan Numbers", Journal of Integer Sequences 26 (2023), Article 23.4.2, Proposition lines 1757-1759, <https://cs.uwaterloo.ca/journals/JIS/VOL26/Getachew/get3.tex>.
