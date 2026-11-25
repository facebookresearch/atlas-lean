# Handlers as homomorphisms from free models

Let $\mathcal{E}$ be an effect theory: a signature of effect operations, each with a parameter set and finitely many argument arities, together with equations between effect terms. It induces a possibly infinitary equational theory.

- **Models.** A model of $\mathcal{E}$ is a set $M$ with, for each operation $\mathrm{op}$, a map $\mathrm{op}_M$ interpreting it, such that the induced operations satisfy the equations. A homomorphism of models is a map commuting with all the operations.
- **Free models.** Models and homomorphisms form a category $\mathrm{Mod}_{\mathcal{E}}$. Its forgetful functor $U : \mathrm{Mod}_{\mathcal{E}} \to \mathbf{Set}$ has a left adjoint $F$, which builds the free model $FA$ on a set $A$ with unit $\eta_A : A \to UFA$. The set $UFA$ represents the computations returning values in $A$, and $UF$ is the monad of the effect. For exceptions it is $X \mapsto X + E$, for nondeterminism $X \mapsto \mathcal{F}^+(X)$ (finite nonempty subsets), and for state $X \mapsto (S \times X)^S$.
- **Handlers.** A handler gives a carrier $M$ with an interpretation of every operation; it is *correct* when these interpretations make $M$ a model of $\mathcal{E}$. Given a correct handler and a map $g : A \to UM$ interpreting returned values, the universal property of the free model yields a unique homomorphism $h : FA \to M$ with $Uh \circ \eta_A = g$. Handling a computation $t \in UFA$ is $Uh(t)$.

For exceptions, the handling construct "try $t$ with $\mathrm{raise}_e \mapsto t_e$" is the homomorphism $X + E \to M$ induced by $g$ on the model whose operation $\mathrm{raise}_e$ is the constant $t_e$. Every homomorphism out of the free model arises in this way.

## Sources

- G. Plotkin and M. Pretnar, "Handlers of algebraic effects", *ESOP 2009*, LNCS 5502, Springer, 2009, pp. 80–94, <https://homepages.inf.ed.ac.uk/gdp/publications/Effect_Handlers.pdf>: Section 2 (handlers as homomorphisms, the exceptions example), Section 3 (effect theories, models, homomorphisms, the free model $FA$ and the monad $UF$), and Section 5.1 (correct handlers induce models; the handling construct is the unique induced homomorphism).
