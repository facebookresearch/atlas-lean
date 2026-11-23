# The $U^2$ norm is the $\ell^4$ norm of the Fourier transform

Let $G$ be a finite abelian group; $\psi$ ranges over its characters, the homomorphisms $G \to \mathbb{C}^\times$, and $\mathbb{E}$ denotes an average over $G$. For every $f : G \to \mathbb{C}$,

$$\|f\|_{U^2} = \Bigl(\sum_{\psi} |\hat f(\psi)|^4\Bigr)^{1/4}, \qquad \hat f(\psi) = |G|^{-1} \sum_x \psi(x) f(x).$$

This is Lemma 2.4 of Gowers (2010) and identity (2.4) of Green and Tao. Both normalise the transform as $\mathbb{E}_x f(x)\overline{\psi(x)}$, which is the one used here composed with $\psi \mapsto \psi^{-1}$; that bijection of the dual group does not change the sum. It is the reason Fourier analysis controls $U^2$ and, by the [generalized von Neumann theorem](norm-ap-count-three-le-gowers-norm-two.md), three-term progressions, but not the higher norms.

## Informally uses

- [Plancherel formula on a finite abelian group](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-transform-on-finite-abelian-groups/dft-plancherel.md): Gowers's proof writes $\|f\|_{U^2}^4 = \langle f * f, f * f \rangle$ and applies Parseval's identity.

## Background

- [Plancherel formula for finite groups](../../../../RepresentationTheory/finite-group-representations/fourier-transform-on-finite-groups/plancherel.md): the non-abelian Fourier transform, whose Plancherel formula reduces to the abelian one when every irreducible representation is a character.

## Sources

- W. T. Gowers, "Decompositions, approximate structure, transference, and the Hahn–Banach theorem", Bull. London Math. Soc. 42 (2010), 573–606; numbering of arXiv:0811.3103, Lemma 2.4.
- B. Green and T. Tao, "An inverse theorem for the Gowers $U^3(G)$ norm", Proc. Edinb. Math. Soc. 51 (2008), 73–153; numbering of arXiv:math/0503014, (2.4).
