# Equilibria of weakest-link and best-shot reliability games

Assume the reliability function $P$ is concave. In a weakest-link game every common effort level up to the smallest stand-alone optimum $\min_i \bar x_i$ is a pure Nash equilibrium (and the profile with all agents at that level is the best one); with identical agents the social optimum is an equilibrium, and liability or negligence rules can make the efficient common level an equilibrium. In a best-shot game every pure Nash equilibrium has at most one agent exerting positive effort, equal to its stand-alone optimum, and the profile where the agent with the highest benefit-cost ratio provides its stand-alone effort is an equilibrium. For two agents, if moreover $P$ is differentiable and strictly concave, equilibrium reliability is at most the socially optimal reliability, and falls strictly short of it whenever the socially optimal effort is positive (Varian 2004, Sections 2, 4.1 and 4.2, Fact 3).

## Proof sketch

Under weakest link, raising effort above the current minimum is wasted and lowering it reduces reliability, so any common level below every stand-alone optimum is stable. Under best shot, only the maximal effort matters, so at most one agent profits from positive effort. A positive social optimum sets the aggregate where $(\sum_i v_i) P' = \min_i c_i$, while an active agent $j$ stops where $v_j P' = c_j$, which with two or more agents is a strictly larger marginal reliability, hence a strictly smaller effort.

## Depends on

- [Varian's system reliability games](varians-system-reliability-games.md)

## Proof depends on

- [Free riding in total-effort reliability games](free-riding-in-total-effort-reliability-games.md)

## Sources

- Hal R. Varian, "System Reliability and Free Riding", Economics of Information Security, Springer, 2004, Sections 2, 4.1 and 4.2 (Fact 3).
