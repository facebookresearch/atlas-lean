# Evolutionary stability of cooperative action rules under indirect reciprocity

In a large well-mixed population, pairs are drawn at random, one as donor and one as recipient. The donor chooses cooperation $C$ (paying cost $c$, giving benefit $b$ to the recipient), defection $D$ (no cost, no benefit) or punishment $P$ (paying cost $\alpha$, imposing cost $\beta$ on the recipient). Every recipient carries a binary reputation, good $G$ or bad $B$. An **action rule** $s : \{G, B\} \to \{C, D, P\}$ prescribes the donor's move as a function of the recipient's reputation, and a **social norm** $n : \{C, D, P\} \times \{G, B\} \to \{G, B\}$ assigns the donor a new reputation from the donor's action and the recipient's reputation; each new reputation is assigned wrongly, and adopted by everyone, with probability $\mu \in [0, 1/2]$, and the **social resolution** is $q = 1 - 2\mu$.

Write $CD$ for the rule that cooperates with good recipients and defects against bad ones, $CP$ for the rule that cooperates with good recipients and punishes bad ones, and $DD$ for unconditional defection.

**Stability conditions.** Among the nine action rules, exactly two that cooperate with good recipients can be evolutionarily stable, and

- under a social norm that stabilizes it (below), $CD$ is evolutionarily stable if and only if $\;q > c/b$;
- under a social norm that stabilizes it (below), $CP$ is evolutionarily stable if and only if $\;q > \max\{c, \alpha\}/(b + \beta)$;
- $DD$ is evolutionarily stable always.

Costly punishment can therefore stabilize cooperation in a regime where $CD$ cannot, namely $\max\{c,\alpha\}/(b+\beta) < q < c/b$. This regime contains admissible values of $q$ exactly when $\alpha/(b+\beta) < c/b$ and $\max\{c,\alpha\} < b+\beta$ (the second condition holds automatically when $b \ge c$), and then punishment extends the stability range of cooperation.

**Which norms work.** A norm stabilizing $CD$ must satisfy: cooperation with a good recipient yields a good reputation; defection against a good recipient yields a bad reputation; defection against a bad recipient yields a good reputation. The remaining three entries are free, except that if $c > \alpha$ the norm must assign a bad reputation to punishing a good recipient, otherwise a donor could keep a good reputation by substituting the cheaper punishment for the prescribed, more expensive cooperation. A norm stabilizing $CP$ must satisfy: cooperation with a good recipient yields a good reputation; defection, against any recipient, yields a bad reputation; punishment of a bad recipient yields a good reputation. The general pattern across all stabilizing norms is the same: following the prescribed action preserves a good reputation, and any deviation that is cheaper than the prescribed action must be met with a bad reputation.

## Expansion

The conditions have the shape of Hamilton-type thresholds with $q = (1-\mu) - \mu$, the difference between the probabilities of a correct and an incorrect assessment, in the role of relatedness. Under $CD$ (with a stabilizing norm) a donor who cooperates pays $c$ now, and the probability of good standing, which earns $b$ later, after cooperating minus that after defecting is $(1-\mu) - \mu = q$; stability against the defecting mutant requires $qb > c$. Under $CP$ the deterrent available to the population is larger, since a donor who loses standing both fails to receive $b$ and suffers $\beta$, which is why the benefit term becomes $b + \beta$; the numerator becomes $\max\{c, \alpha\}$ because the rule must resist two deviations at once, shirking the cooperation and shirking the punishment. The free entries in the norms matter for counting how many norms work (the analysis enumerates all second-order norms), not for the thresholds. Stability here is the standard one-population condition against a rare mutant rule, and $DD$'s unconditional stability is the usual statement that defection is always a Nash equilibrium of a donation game.

## Sources

- H. Ohtsuki, Y. Iwasa and M. A. Nowak, "Indirect reciprocity provides only a narrow margin of efficiency for costly punishment", Nature 457 (2009), 79–82, main text (stability conditions for $CD$, $CP$ and $DD$; characterization of stabilizing social norms, Fig. 2), <https://doi.org/10.1038/nature07601>, PMCID PMC2614697.
