# Fibonacci closed form of the sequence $a_n$

Let $(a_n)_{n \ge 0}$ be real numbers with
$a_0 = -8\sqrt{5}/250$, $a_1 = (25 - 4\sqrt{5})/250$ and $a_{n+1} = a_n + a_{n-1}$ for $n \ge 1$,
and write $F_m$ for the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then for every $n \ge 0$,

$$a_{n+1} = \frac{25 - 4\sqrt{5}}{250} F_{n+1} - \frac{8\sqrt{5}}{250} F_n.$$

The paper states $a_n = \frac{25 - 4\sqrt{5}}{250} F_n - \frac{8\sqrt{5}}{250} F_{n-1}$ for all
$n \ge 0$ with the convention $F_{-1} = 1$; its case $n = 0$ is the initial value $a_0$.

## Sources

- Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1, Lemma 2.3 (`fq-2024-tonien10292023-lem-2.3`).
