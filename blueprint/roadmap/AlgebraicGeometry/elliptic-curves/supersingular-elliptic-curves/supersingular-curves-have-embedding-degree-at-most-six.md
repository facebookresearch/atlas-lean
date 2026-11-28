# Supersingular curves have small embedding degree

For a supersingular elliptic curve over $\mathbb{F}_q$ there is $m\in\{1,2,3,4,6\}$ with $\pi_q^m=[s]$ for an integer $s$ such that the exponent of $E(\mathbb{F}_q)$ divides $q^m-1$; hence every prime $r\mid\#E(\mathbb{F}_q)$ has $r\mid q^m-1$, and the least $k\ge1$ with $r\mid q^k-1$ is at most $6$.

**Theorem.** Let $q=p^n$ with $p$ prime and let $E$ be a supersingular elliptic curve over $\mathbb{F}_q$, with $q$-power Frobenius endomorphism $\pi_q$. There are $m\in\{1,2,3,4,6\}$ and $s\in\mathbb{Z}$ such that $\pi_q^m=[s]$ in $\operatorname{End}(E)$ and the exponent of the group $E(\mathbb{F}_q)$ divides $q^m-1$. The value of $m$ obtained from the trace of $\pi_q$ can be taken in $\{1,2\}$ unless $q$ is a square ($m=3$), a power of $2$ ($m=4$) or a power of $3$ ($m=6$). Consequently every prime $r$ dividing $\#E(\mathbb{F}_q)$ satisfies $r\ne p$ and $r\mid q^m-1$, so the least $k\ge1$ with $r\mid q^k-1$ is at most $6$.

## Depends on

- [Supersingular elliptic curves](is-supersingular.md)
- [Embedding degree](../../../ComputerScience/cryptography/public-key/advanced-encryption-and-pairings/embedding-degree-and-pairing-attacks/embedding-degree.md)
- [Frobenius trace](../point-counts-and-frobenius-traces/frobenius-trace.md)

## Proof depends on

- [Waterhouse's theorem on Frobenius traces](../point-counts-and-frobenius-traces/exists-is-elliptic-frobenius-trace-eq-if.md)

## Expansion

Galbraith's route: the trace $t$ of a supersingular curve is divisible by $p$, so by Waterhouse's classification $t\in\{0,\pm\sqrt q,\pm2\sqrt q,\pm\sqrt{2q},\pm\sqrt{3q}\}$, the last two only for $q$ a power of $2$ or of $3$. For the complex roots $\alpha$ of $P(T)=T^2-tT+q$, each non-square factor of $\tfrac1qP(T\sqrt q)$ divides $\Phi_m(T^2)$ for some $m\in\{1,2,3,4,6\}$ (Lemma 9.11.8), so $\alpha^m$ is an integer $s$ with $s^2=q^m$, the same for both roots. Granting the resulting relation $\pi_q^m=[s]$ in $\operatorname{End}(E)$ (the passage from the roots of $P$ to the endomorphism is a prerequisite below), $\deg\pi_q^m=q^m=s^2$. As $\pi_q$ fixes $E(\mathbb{F}_q)$ pointwise, $[s-1]$ kills $E(\mathbb{F}_q)$, and $s-1$ divides $s^2-1=q^m-1$. A prime $r\mid\#E(\mathbb{F}_q)$ divides the exponent by Cauchy's theorem, and $r\ne p$ since $E$ has no point of order $p$. Galbraith leaves the corollary as an exercise. Prerequisites still to add: the criterion that $E$ is supersingular exactly when $p$ divides its Frobenius trace $t$ (Galbraith, Theorem 9.11.2); the characteristic polynomial of Frobenius as a relation $\pi_q^2-[t]\pi_q+[q]=0$ in $\operatorname{End}(E)$, and the passage from its roots to $\pi_q^m=[s]$, including the repeated-root case $t=\pm2\sqrt q$. Small embedding degree makes the MOV/Frey–Rück reduction land in a small field; it does not by itself determine the cost of the resulting discrete logarithm.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Theorem 9.11.2, Lemma 9.11.8, Corollary 9.11.9 and Theorem 26.4.2.
