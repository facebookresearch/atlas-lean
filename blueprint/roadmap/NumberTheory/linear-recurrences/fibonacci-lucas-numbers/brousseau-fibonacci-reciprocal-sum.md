# Brousseau's alternating series of reciprocal Fibonacci squares

Let $F_n$ denote the
Fibonacci numbers, with $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$. For every positive
integer $q$, the real series
$\sum_{k \ge 1} (-1)^{k-1} \frac{F_{2k+q}}{F_k^2 \, F_{k+q}^2}$ is unconditionally summable,
with sum $\frac{1}{F_q} \sum_{k=1}^{q} \frac{(-1)^{k-1}}{F_k^2}$.

Adegoke's generalization has a further integer parameter $n$ and assumes that $q$ is even or
$nq$ is odd; this is its case $n = 1$, in which that assumption holds for every positive $q$.

## Sources

- Kunle Adegoke, "Generalizations of the Reciprocal Fibonacci-Lucas Sums of Brousseau," Journal of Integer Sequences 21 (2018), `https://cs.uwaterloo.ca/journals/JIS/VOL21/Adegoke/ade3.tex`, live and bundled source-file SHA-256 `8feb3648f4ab8f2da4d383821f763b4b57316a8f46343082a2c0d7682912f5d7`; controlling theorem, equation, and specialization at lines 1135–1148 with exact-span SHA-256 under LF joining without a terminal LF `360a38704aab45f8e89f64fb8ffc5f865c5da5316796e5ec28c650318b343dd1`; original reference: Brother Alfred Brousseau, "Fibonacci-Lucas Infinite Series — Research Topic," Fibonacci Quarterly 7 (1969), 211–217, Formula (6), cited at source line 1414; task id: `jis_grounded_50e651872ff01364d67794b1__brousseau_fibonacci_reciprocal_sum`.
