# The global logic for choreographies

The global logic describes choreographies of the global calculus in a given state, with action modalities, an eventually operator, a spatial conjunction and first-order quantification.

**Global logic.** Formulas are

$$
\phi ::= \exists x.\,\phi \mid \phi \land \phi \mid \neg \phi \mid \langle \ell \rangle \phi \mid \mathsf{end} \mid e_1@A = e_2@B \mid \phi \mid \phi \mid \Diamond \phi,
$$

where $\exists$ ranges over channels, participants, labels and expression placeholders. Satisfaction $C \models_\sigma \phi$: $\mathsf{end}$ is true if $C \equiv \mathbf 0$; $e_1@A = e_2@B$ if both evaluate in $\sigma$ to the same value; $\langle \ell \rangle \phi$ if $(\sigma, C) \xrightarrow{\ell} (\sigma', C')$ with $C' \models_{\sigma'} \phi$; $\Diamond \phi$ if $(\sigma, C) \to^* (\sigma', C')$ with $C' \models_{\sigma'} \phi$; $\phi \mid \chi$ if $C \equiv C_1 \mid C_2$ with $C_1 \models_\sigma \phi$ and $C_2 \models_\sigma \chi$; the Boolean connectives and $\exists$ (for some value of the appropriate sort) as usual.

## Depends on

- [The global calculus of choreographies](global-calculus-and-global-logic.md)

## Proof depends on

None.

## Expansion

The logic extends Hennessy–Milner logic with first-order quantification, the eventually operator of temporal logic and a spatial composition operator in the style of separation and spatial logics; always, next and box modalities are derived.

## Sources

- Marco Carbone, Davide Grohmann, Thomas T. Hildebrandt and Hugo A. López, "A Logic for Choreographies", in *Proceedings of the 3rd Workshop on Programming Language Approaches to Concurrency and Communication-cEntric Software (PLACES 2010)*, Electronic Proceedings in Theoretical Computer Science 69, 2011, pp. 29–43, <https://doi.org/10.4204/EPTCS.69.3>; read in arXiv:1110.4159v1, <https://arxiv.org/abs/1110.4159v1>: Sections 3.1–3.2 with Definition 3.7 (syntax and satisfaction of the global logic), in the numbering of that version.
