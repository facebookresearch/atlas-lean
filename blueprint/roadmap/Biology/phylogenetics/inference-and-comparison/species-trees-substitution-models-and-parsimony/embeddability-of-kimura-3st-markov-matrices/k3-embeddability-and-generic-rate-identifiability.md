# Embeddability and rate identifiability of Kimura 3ST Markov matrices

**Setting.** A $4\times4$ *Kimura 3ST* (K3) matrix has the form

$$K(a,b,c,d)=\begin{pmatrix}a&b&c&d\\ b&a&d&c\\ c&d&a&b\\ d&c&b&a\end{pmatrix},$$

and is Markov when $a,b,c,d\ge0$ and $a+b+c+d=1$. Every K3 matrix is diagonalized by the fixed Hadamard matrix $S$, $K(a,b,c,d)=S\,\mathrm{diag}(1,x,y,z)\,S^{-1}$ with $x=a+b-c-d$, $y=a-b+c-d$, $z=a-b-c+d$, so K3 Markov matrices are the tetrahedron in $(x,y,z)$-space with vertices $(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)$. A Markov matrix $M$ is *embeddable* if $M=e^Q$ for some rate matrix $Q$ (nonnegative off-diagonal entries, zero row sums), and *K3-embeddable* if such a $Q$ can be taken of K3 form.

**Theorem.** Let $M$ be a K3 Markov matrix with eigenvalues $1,x,y,z$.

1. $M$ has a real logarithm of K3 form iff $x,y,z>0$, and then it is the principal logarithm $\operatorname{Log}M=S\,\mathrm{diag}(0,\log x,\log y,\log z)\,S^{-1}$.
2. $M$ is K3-embeddable iff $x,y,z>0$ and

$$x\ge yz,\qquad y\ge xz,\qquad z\ge xy .$$

3. If $x,y,z$ are pairwise distinct, every real logarithm of $M$ is $\operatorname{Log}M$, so $M$ is embeddable iff it is K3-embeddable iff the conditions in item 2 hold, and the generator (the substitution rates) is unique.
4. *(Genericity.)* For the Kimura 3ST model, K3-embeddability and identifiability of rates hold for almost every embeddable matrix. For the Kimura 2ST model ($c=d$) neither property is generic among embeddable matrices, and for Jukes–Cantor ($b=c=d$) every embeddable matrix is JC-embeddable but rate identifiability is not generic: with repeated negative eigenvalues there are embeddable matrices with several distinct Markov generators.
5. *(Volumes in eigenvalue coordinates.)* The whole tetrahedron has volume $8/3$; the region $a\ge b,c,d$ has volume $2/3$, the region with positive eigenvalues $1/2$, the diagonally dominant region $a\ge b+c+d$ has volume $1/3$, and the embeddable matrices have volume $1/4$ (about $9.4\%$ of all K3 Markov matrices), of which about $0.20336$ lies in the diagonally dominant region.

## Expansion

If $Q$ is a logarithm of $M$, eigenvectors of $Q$ are eigenvectors of $M$ with eigenvalues exponentiated; with distinct eigenvalues the eigenvectors are the columns of $S$, so any real logarithm is simultaneously diagonalized by $S$, has K3 form, and real eigenvalues force the principal branch. Writing $\operatorname{Log}M=K(\alpha,\beta,\gamma,\delta)$, the off-diagonal entries are $\tfrac14(\log x-\log y-\log z)$-type combinations, e.g. $\beta=\tfrac14\log(x/(yz))$, so nonnegativity of the rates is exactly $x\ge yz$, $y\ge xz$, $z\ge xy$. Repeated eigenvalues form a measure-zero set in the 3ST tetrahedron but are forced by the 2ST and JC constraints, where non-principal complex branches $\log\lambda+2\pi ik$ can produce additional real Markov generators. The volumes are elementary integrals over the regions cut out by these inequalities.

## Sources

- Jordi Roca-Lacostena, Jesús Fernández-Sánchez, "Embeddability of Kimura 3ST Markov matrices", Journal of Theoretical Biology 445 (2018), 128–135, <https://doi.org/10.1016/j.jtbi.2018.02.005>. Published version of arXiv:1703.02263, cited next; locators there refer to the arXiv version.
- J. Roca-Lacostena, J. Fernández-Sánchez, "Embeddability of Kimura 3ST Markov matrices", arXiv:1703.02263 (2017), Lemma 2.4, Theorem 3.3, Lemma 3.4, Corollary 3.5, Example 3.6, Theorem 3.9 and Theorem 4.1. <https://doi.org/10.48550/arXiv.1703.02263>
