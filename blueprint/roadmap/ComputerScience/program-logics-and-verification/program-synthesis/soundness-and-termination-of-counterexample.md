# Soundness and termination of counterexample-guided inductive synthesis

Let $C$ be a set of candidate programs, $X$ a set of inputs and $\varphi(c, x)$ a specification. CEGIS maintains a finite set $E \subseteq X$ of examples, starting from $E = \emptyset$. In each round an inductive synthesizer returns some $c \in C$ with $\varphi(c, x)$ for all $x \in E$, or reports that none exists; a verifier then either certifies $\forall x \in X.\, \varphi(c, x)$ or returns $x \in X$ with $\neg \varphi(c, x)$, which is added to $E$. Every candidate the loop returns as certified satisfies the specification on all inputs. If $C$ is finite, the loop terminates, since each counterexample eliminates the current candidate and all later candidates differ from it; it returns a solution if one exists in $C$ and reports failure otherwise.

## Depends on

- [Syntax-guided synthesis problems](syntax-guided-synthesis-problems.md)

## Sources

- A. Solar-Lezama, *Program Synthesis by Sketching*, PhD thesis, University of California, Berkeley, 2008
- R. Alur et al., "Syntax-guided synthesis", *FMCAD 2013*, IEEE, 2013
