# Inverse theorem for the $U^2$ norm

Let $G$ be a finite abelian group; $\psi$ ranges over its characters, the homomorphisms $G \to \mathbb{C}^\times$, and $\mathbb{E}$ denotes an average over $G$. Let $f : G \to \mathbb{C}$ with $\mathbb{E} |f|^2 \le 1$ and let $0 \le c \le \|f\|_{U^2}$. Then some character $\psi$ satisfies

$$|\mathbb{E}_x f(x)\overline{\psi(x)}| \ge c^2.$$

This is Proposition 2.7 of Gowers (2010), stated there for $c > 0$; the case $c = 0$ is trivial. Conversely, correlation with a character forces a large $U^2$ norm, so characters "explain" the $U^2$ norm. Green and Tao's Proposition 2.2 is the same statement in the form $\|f\|_{u^2} \le \|f\|_{U^2} \le \|f\|_{u^2}^{1/2}$ for bounded $f$. For $U^3$ characters no longer suffice and one needs [quadratic phases](u3-inverse-f5.md).

## Informally uses

- [The $U^2$ norm is the $\ell^4$ norm of the Fourier transform](gowers-norm-two-eq.md): the first step, $c^2 \le \|\hat f\|_4^2$.
- [Plancherel formula on a finite abelian group](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-transform-on-finite-abelian-groups/dft-plancherel.md): in $\|\hat f\|_4^2 \le \|\hat f\|_\infty \|\hat f\|_2 \le \|\hat f\|_\infty$ the last step is Parseval, $\|\hat f\|_2 = \|f\|_2 \le 1$.

## Sources

- W. T. Gowers, "Decompositions, approximate structure, transference, and the Hahn–Banach theorem", Bull. London Math. Soc. 42 (2010), 573–606; numbering of arXiv:0811.3103, Proposition 2.7.
- B. Green and T. Tao, "An inverse theorem for the Gowers $U^3(G)$ norm", Proc. Edinb. Math. Soc. 51 (2008), 73–153; numbering of arXiv:math/0503014, Proposition 2.2.
