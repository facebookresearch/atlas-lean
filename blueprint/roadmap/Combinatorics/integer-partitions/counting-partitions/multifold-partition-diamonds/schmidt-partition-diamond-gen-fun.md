# Generating function of Schmidt type $d$-fold partition diamonds

Let $d \ge 1$. A Schmidt
type $d$-fold partition diamond is a finitely supported sequence $(a_p)_{p \ge 0}$ of natural
numbers such that $a_{k(d+1)} \ge a_{k(d+1)+f} \ge a_{(k+1)(d+1)}$ for all $k \ge 0$ and all
$f$ with $1 \le f \le d$; its weight is the sum of its links $a_{k(d+1)}$, $k \ge 0$. Let
$s_d(w)$ be the number of such diamonds of weight $w$, and let
$S_d(q) = \sum_{w \ge 0} s_d(w) q^w \in \mathbb{Z}[[q]]$. Then for all natural numbers $n \le N$,
the coefficient of $q^n$ in $S_d(q) \prod_{m=1}^{N} (1 - q^m)^{d+1}$ equals the coefficient of
$q^n$ in $\prod_{m=1}^{N} E_d(q^m, 1)$, where $E_d$ is the Euler–Mahonian polynomial.

Since every factor $E_d(q^m, 1)/(1 - q^m)^{d+1}$ with $m > N$ is $1$ modulo $q^{N+1}$, the
statement for all $N$ is equivalent to $S_d(q) = \prod_{m \ge 1} E_d(q^m, 1)/(1 - q^m)^{d+1}$.

## Sources

- Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds Revisited*, INTEGERS 26 (2026), Article A13, Corollary 1 (`integers-2026-A13-cor-1`), quoting Dockery-Jameson-Sellers-Wilson.
