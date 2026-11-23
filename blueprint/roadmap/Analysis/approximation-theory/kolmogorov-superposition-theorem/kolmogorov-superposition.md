# Kolmogorov superposition theorem

Let $n \ge 2$. There are continuous functions
$\psi_{q,p} : [0,1] \to \mathbb{R}$ for $0 \le q \le 2n$ and $0 \le p < n$, depending only on
$n$, such that for every continuous function $f : [0,1]^n \to \mathbb{R}$ there are continuous
functions $\varphi_q : \mathbb{R} \to \mathbb{R}$ for $0 \le q \le 2n$ with
$f(x) = \sum_{q=0}^{2n} \varphi_q\left(\sum_{p=0}^{n-1} \psi_{q,p}(x_p)\right)$ for every
$x = (x_0, \dots, x_{n-1}) \in [0,1]^n$.

## Sources

- Kolmogorov superposition theorem, A. N. Kolmogorov, Dokl. Akad. Nauk SSSR 114 (1957) 953–956, refined Arnold 1957; see Braun–Griebel, Acta Numer. 2009 review; Lean is n ≥ 2 exact cardinal Fin (2n+1) with inner ψ in C(Icc 0 1, ℝ) independent of f and outer φ in C(ℝ, ℝ), compact-source specialization [0, 1]^n as Fin n → Icc.
