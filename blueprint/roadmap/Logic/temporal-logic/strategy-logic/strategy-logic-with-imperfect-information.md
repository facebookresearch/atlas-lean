# Strategy logic with imperfect information

Strategy logic with imperfect information $\mathrm{SL}_{ii}$ annotates each strategy quantifier with an observation $o$, and ranges it only over strategies that are uniform for $o$: strategies that choose the same action after any two finite plays that look the same under $o$, with synchronous perfect recall.

**Syntax.** Fix finite sets $\mathrm{AP}$ of atomic propositions, $\mathrm{Ag}$ of agents, $\mathrm{Var}$ of variables and $\mathrm{Obs}$ of observation symbols. Formulas are

$$
\varphi ::= p \mid \neg\varphi \mid \varphi \vee \varphi \mid X\varphi \mid \varphi\, U \varphi \mid \exists^{o} x\,\varphi \mid (a, x)\varphi
$$

with $p \in \mathrm{AP}$, $x \in \mathrm{Var}$, $o \in \mathrm{Obs}$, $a \in \mathrm{Ag}$, and $\forall^o x\,\varphi = \neg\exists^o x\,\neg\varphi$. Free variables, free agents and sentences are as in [strategy logic](strategy-logic.md).

**Models.** A concurrent game structure with imperfect information is $\mathcal{G} = (\mathrm{Ac}, V, E, \ell, v_\iota, \mathcal{O})$ with a finite nonempty set $\mathrm{Ac}$ of actions, a finite nonempty set $V$ of positions, a transition function $E : V \times \mathrm{Ac}^{\mathrm{Ag}} \to V$, a labeling $\ell : V \to 2^{\mathrm{AP}}$, an initial position $v_\iota$, and an observation interpretation $\mathcal{O}$ sending each $o \in \mathrm{Obs}$ to an equivalence relation $\sim_o$ on $V$.

**Semantics.** Two finite plays are $o$-indistinguishable when they have the same length and are pointwise $\sim_o$-equivalent (synchronous perfect recall). An *$o$-strategy* is a map from finite plays to actions that takes the same value on $o$-indistinguishable plays. The formula $\exists^o x\,\varphi$ is true after a finite play $\rho$ under an assignment $\chi$ if some $o$-strategy $\sigma$ makes $\varphi$ true under $\chi[x \mapsto \sigma]$; bindings and temporal operators are as in strategy logic, temporal operators being evaluated on the outcome of the strategies assigned to the agents. For a sentence, $\mathcal{G} \models \Phi$ means that $\Phi$ is true after the one-position play $v_\iota$.

The *model-checking problem* for $\mathrm{SL}_{ii}$ takes a sentence $\Phi$ and a finite structure $\mathcal{G}$ (with the sets $\mathrm{AP}$, $\mathrm{Ag}$, $\mathrm{Var}$, $\mathrm{Obs}$ part of the input) and asks whether $\mathcal{G} \models \Phi$.

## Depends on

- [Strategy logic](strategy-logic.md)

## Proof depends on

None.

## Remarks

Unlike imperfect-information versions of ATL, observations are attached to strategy quantifiers rather than to players, so one agent may be bound to strategies of different observational power in different parts of a formula. When every $\sim_o$ is the identity, every strategy is uniform and $\mathrm{SL}_{ii}$ becomes strategy logic interpreted on finite structures.

## Sources

- R. Berthon, B. Maubert, A. Murano, S. Rubin and M. Y. Vardi, "Strategy logic with imperfect information", in *32nd Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2017)*, IEEE, 2017, pp. 1–12, doi:10.1109/LICS.2017.8005136; read as the extended version arXiv:1805.12592v2, <https://arxiv.org/abs/1805.12592v2>: Section II (syntax, concurrent game structures with imperfect information, $o$-strategies, semantics and the model-checking problem).
