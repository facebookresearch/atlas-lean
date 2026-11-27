# Gödel's second incompleteness theorem for Peano arithmetic

Write $\mathrm{PA} \vdash \sigma$ for derivability of a sentence $\sigma$ from the Peano axioms in the classical natural deduction calculus (sentences regarded as formulas over the infinite set $\mathbb{N}$ of variable names), $\ulcorner \sigma \urcorner$ for the Gödel number of $\sigma$ under the pairing numbering of sentences, and $\overline{n} = S^n(0)$ for the numeral of $n$. For a formula $\mathrm{Prov}(x)$ with one free variable, $\mathrm{Prov}(\overline{n})$ is the sentence obtained by substituting $\overline{n}$ for $x$.

The following holds: there are a formula $\mathrm{Prov}(x)$ with one free variable and a sentence $\mathrm{Con}_{\mathrm{PA}}$ such that

1. for every sentence $\sigma$, $\mathrm{PA} \vdash \sigma$ if and only if $\mathrm{PA} \vdash \mathrm{Prov}(\overline{\ulcorner \sigma \urcorner})$;
2. for every sentence $\sigma$, $\mathbb{N} \models \mathrm{Prov}(\overline{\ulcorner \sigma \urcorner})$ if and only if $\mathrm{PA} \vdash \sigma$;
3. (D1) for every sentence $\sigma$, if $\mathrm{PA} \vdash \sigma$ then $\mathrm{PA} \vdash \mathrm{Prov}(\overline{\ulcorner \sigma \urcorner})$;
4. (D2) for all sentences $\sigma, \tau$, $\mathrm{PA} \vdash \mathrm{Prov}(\overline{\ulcorner \sigma \to \tau \urcorner}) \to \bigl(\mathrm{Prov}(\overline{\ulcorner \sigma \urcorner}) \to \mathrm{Prov}(\overline{\ulcorner \tau \urcorner})\bigr)$;
5. (D3) for every sentence $\sigma$, $\mathrm{PA} \vdash \mathrm{Prov}(\overline{\ulcorner \sigma \urcorner}) \to \mathrm{Prov}\bigl(\overline{\ulcorner \mathrm{Prov}(\overline{\ulcorner \sigma \urcorner}) \urcorner}\bigr)$;
6. there is a sentence $G$ with $\mathrm{PA} \vdash G \leftrightarrow \neg \mathrm{Prov}(\overline{\ulcorner G \urcorner})$;
7. $\mathrm{Con}_{\mathrm{PA}}$ is the sentence $\neg \mathrm{Prov}(\overline{\ulcorner \bot \urcorner})$;
8. if $\mathrm{PA} \nvdash \bot$, then $\mathrm{PA} \nvdash \mathrm{Con}_{\mathrm{PA}}$.

The content is the existence of a provability formula for Peano arithmetic itself, with this concrete coding, satisfying the derivability conditions and the diagonal property; the derivation of item 8 from such conditions alone is the abstract Hilbert–Bernays–Löb argument.

## Sources

- K. Gödel, "Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I", *Monatshefte für Mathematik und Physik* 38 (1931), 173-198.
- H. Enderton, *A Mathematical Introduction to Logic*, 2nd ed., Academic Press, 2001, §3.7.
- G. Boolos, J. Burgess, and R. Jeffrey, *Computability and Logic*, 5th ed., Cambridge University Press, 2007, Chapter 18.
