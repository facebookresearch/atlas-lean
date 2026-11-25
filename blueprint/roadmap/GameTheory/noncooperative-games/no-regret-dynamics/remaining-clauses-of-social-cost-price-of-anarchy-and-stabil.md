# Price of anarchy and price of stability

Social cost is defined on a separate page, listed under the dependencies; it is reused, not restated. This node defines
the inefficiency measures.

For a cost game with finitely many players and finite nonempty strategy sets, social cost $C$ and $\mathrm{OPT} = \min_s C(s) > 0$ (attained, since
there are finitely many profiles), and a nonempty class $\mathcal{E}$ of equilibria, the price of anarchy is $\sup_{e \in \mathcal{E}} C(e)/\mathrm{OPT}$ and the
price of stability is $\inf_{e \in \mathcal{E}} C(e)/\mathrm{OPT}$. For pure Nash equilibria $C(e)$ is the social cost of the profile; for mixed, correlated and
coarse correlated equilibria it is the expected social cost under the equilibrium distribution, with mixed equilibria taken for the
payoffs $u_i = -c_i$. The measures are undefined when the class is empty.

## Depends on

- [Social cost](social-cost.md)
- [Pure Nash equilibrium](../potential-games/is-pure-nash.md)
- [Mixed Nash equilibrium](../nash-s-theorem/is-mixed-nash.md)
- [Correlated equilibrium](../correlated-equilibria/is-correlated-eq.md)
- [Coarse correlated equilibrium](is-coarse-correlated-eq.md)

## Sources

- AGTA Lecture 12: Inefficiency of Equilibria — University of Edinburgh, Algorithmic Game Theory and its Applications (2025), slides "Price of Anarchy (Koutsoupias and Papadimitriou 1999)" (pure, mixed and correlated versions) and "Price of Stability (Anshelevich et al. 2006)". <https://opencourse.inf.ed.ac.uk/sites/default/files/2025-02/agta_-_lecture_12_-_inefficiency_of_equilibria.pdf>
- Intrinsic Robustness of the Price of Anarchy — Tim Roughgarden, Section 1 (the price of anarchy as the ratio of the largest equilibrium cost to the optimal cost). <http://www.math.uwaterloo.ca/~cswamy/courses/co759/agt-material/robust-roughgarden.pdf>
