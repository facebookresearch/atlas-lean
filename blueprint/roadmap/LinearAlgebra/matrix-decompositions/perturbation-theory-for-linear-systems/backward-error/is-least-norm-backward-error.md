# Backward error of an approximate solution

Let $A$ be a bounded operator on an inner product space (for instance a square matrix with the 2-norm), $b$ a vector and $\hat x \ne 0$ an approximate solution of $Ax = b$, with residual $r = A\hat x - b$. The smallest $\|E\|$ such that $(A + E)\hat x = b$ is

$$\frac{\|r\|}{\|\hat x\|},$$

attained by $E = -r\,\hat x^*/\|\hat x\|^2$, of rank at most one (zero when $r = 0$) (J. W. Demmel, Math 221 Lecture 3 notes, UC Berkeley, 2024; J. L. Rigal and J. Gaches, *On the compatibility of a given solution with the data of a linear system*, J. ACM 14 (1967), 543–548). So $\hat x$ exactly solves a nearby system when $\|r\|$ is small compared with $\|\hat x\|$ (compared with $\|A\|\,\|\hat x\|$, when $\|A\| > 0$, for a relative statement), which is the most one can ask when the entries of $A$ are uncertain; a small residual alone does not suffice when $\hat x$ is small. The lower bound $\|r\| \le \|E\|\,\|\hat x\|$ holds in every operator norm; the inner product is used only to build the minimiser, the operator $y \mapsto -\langle \hat x, y \rangle\, r / \|\hat x\|^2$.
