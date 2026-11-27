# Natural deduction for intuitionistic propositional logic

Formulas of intuitionistic propositional logic (IPC) are built from propositional variables and $\bot$ with $\wedge$, $\vee$ and $\to$; $\neg\varphi$ abbreviates $\varphi \to \bot$. A *context* $\Gamma$ is a finite set of formulas. The derivability relation $\Gamma \vdash \varphi$ is the least relation closed under the axiom $\Gamma, \varphi \vdash \varphi$ and the rules

- ($\wedge$I) from $\Gamma \vdash \varphi$ and $\Gamma \vdash \psi$ infer $\Gamma \vdash \varphi \wedge \psi$; ($\wedge$E) from $\Gamma \vdash \varphi \wedge \psi$ infer $\Gamma \vdash \varphi$ and $\Gamma \vdash \psi$;
- ($\vee$I) from $\Gamma \vdash \varphi$ or $\Gamma \vdash \psi$ infer $\Gamma \vdash \varphi \vee \psi$; ($\vee$E) from $\Gamma, \varphi \vdash \rho$, $\Gamma, \psi \vdash \rho$ and $\Gamma \vdash \varphi \vee \psi$ infer $\Gamma \vdash \rho$;
- ($\to$I) from $\Gamma, \varphi \vdash \psi$ infer $\Gamma \vdash \varphi \to \psi$; ($\to$E) from $\Gamma \vdash \varphi \to \psi$ and $\Gamma \vdash \varphi$ infer $\Gamma \vdash \psi$;
- ($\bot$E) from $\Gamma \vdash \bot$ infer $\Gamma \vdash \varphi$.

For an infinite set $\Gamma$, $\Gamma \vdash \varphi$ means $\Gamma_0 \vdash \varphi$ for some finite $\Gamma_0 \subseteq \Gamma$. Adding the axioms $\bot \to \psi$ (ex falso) to natural deduction without ($\bot$E), with $\bot$ a distinguished atom, gives the same derivable sequents: ($\bot$E) derives $\bot \to \psi$ by ($\to$I), and conversely from $\Gamma \vdash \bot$ the axiom $\bot \to \psi$ and ($\to$E) give $\Gamma \vdash \psi$. Derivability is closed under weakening and under substitution of formulas for variables.

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 2.2: Definition 2.2.4 with Figure 2.1 (the rules), and Lemma 2.2.7 (weakening and substitution).
