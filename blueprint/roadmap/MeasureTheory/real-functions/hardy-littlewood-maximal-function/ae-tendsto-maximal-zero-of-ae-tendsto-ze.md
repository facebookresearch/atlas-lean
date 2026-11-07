# Maximal functions of bounded a.e.-null sequences tend to zero a.e

Let
$(f_n)_{n \in \mathbb{N}}$ be a sequence of functions $f_n : \mathbb{R} \to \mathbb{R}$, each
Lebesgue measurable on $[0,1]$, such that $f_n(x) \in [0,1]$ for every $n$ and every
$x \in [0,1]$, and $f_n(x) \to 0$ as $n \to \infty$ for almost every $x \in [0,1]$. For
$x \in [0,1]$ let

$$Mf_n(x) = \sup_I \frac{1}{|I|} \int_I |f_n(y)|\,dy,$$

where the supremum is taken over all closed intervals $I = [a,b]$ with $a < b$ and
$x \in I \subseteq [0,1]$, and $|I| = b - a$. Then $Mf_n(x) \to 0$ as $n \to \infty$ for almost
every $x \in [0,1]$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration; Classical measure theory), `benchmark/level2/ma_proofbench_l2_74.lean` at openbmb/ma-proofbench@31bab4c.
