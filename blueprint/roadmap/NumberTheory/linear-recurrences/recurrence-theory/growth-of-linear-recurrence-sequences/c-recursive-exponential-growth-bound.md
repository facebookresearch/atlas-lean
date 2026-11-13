# Exponential growth bound for C-recursive sequences

Let $t : \mathbb{N} \to \mathbb{C}$ be
C-recursive: there are an order $k \ge 1$ and complex numbers $c_0, \dots, c_{k-1}$ with
$t(n+k) = \sum_{i=0}^{k-1} c_i \, t(n+i)$ for all $n \in \mathbb{N}$. Then there is an integer
$g \ge 1$ such that $|t(n)| < g^{n+1}$ for all $n \in \mathbb{N}$.

## Sources

- M. Prunescu and J. M. Shunia, "On Modular Representations of C-Recursive Integer Sequences," Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma (quoting Prunescu and Sauras-Altuzarra, Lemma 4), lines 166–167, https://cs.uwaterloo.ca/journals/JIS/VOL28/Prunescu/prunescu3.tex
