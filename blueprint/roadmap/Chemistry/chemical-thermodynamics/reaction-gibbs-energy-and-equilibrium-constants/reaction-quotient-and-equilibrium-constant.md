# Reaction quotient and thermodynamic equilibrium constant

For a reaction with stoichiometric numbers $\nu_i$, the reaction quotient is $Q_{\mathrm{rxn}}=\prod_i a_i^{\nu_i}$, and the thermodynamic equilibrium constant $K$ is its value in a state of reaction equilibrium.

Consider a reaction among species $i=1,\dots,N$ written with stoichiometric numbers $\nu_i\in\mathbb{R}$,
positive for products and negative for reactants, and let $a_i>0$ be the
[relative activities](chemical-potential-in-terms-of-relative-activity.md) of the species at temperature $T$
for chosen standard states. The **reaction quotient** is the dimensionless proper quotient

$$Q_{\mathrm{rxn}}=\prod_{i=1}^N a_i^{\nu_i},\qquad \ln Q_{\mathrm{rxn}}=\sum_{i=1}^N\nu_i\ln a_i .$$

It is a function of temperature, pressure and composition; it can change as the reaction advances, and stays
fixed when every participating species has a fixed activity (for example, only pure solids at fixed $T$ and $p$).
The **thermodynamic equilibrium constant** is $K=\prod_i (a_i)_{\mathrm{eq}}^{\nu_i}$, the value of
$Q_{\mathrm{rxn}}$ at a state of reaction equilibrium of this reaction, at the given $T$ and with the same
standard states. $K$ depends on the reaction equation (scaling every $\nu_i$ by $c>0$ replaces $K$ by $K^c$) and
on the choice of standard states, and it must be computed with the same standard states as any standard quantity
it is compared with.

## Context

Undergraduate chemical thermodynamics; the quotient enters the Nernst equation of galvanic cells and the electrochemical equilibrium constants of redox reactions.

## Depends on

- [Chemical potential in terms of relative activity](chemical-potential-in-terms-of-relative-activity.md)

## Proof depends on

None.

## Expansion

A definition. The logarithmic form follows from $\ln\prod a_i^{\nu_i}=\sum\nu_i\ln a_i$ for positive $a_i$. That every state of reaction equilibrium of a given reaction at a given $T$ has the same quotient is a theorem, [the standard reaction Gibbs energy and the equilibrium constant](standard-reaction-gibbs-energy-and-equilibrium-constant.md); the definition of $K$ presupposes such a state.

## Sources

- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 11.8.1, Eqs. 11.8.5–11.8.7 (reaction quotient) and Eq. 11.8.9 (definition of $K$). [Section 11.8.1](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/11%3A_Reactions_and_Other_Chemical_Processes/11.08%3A_The_Thermodynamic_Equilibrium_Constant)
