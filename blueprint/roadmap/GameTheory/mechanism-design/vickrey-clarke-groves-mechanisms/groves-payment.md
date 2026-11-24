# Groves payment

Throughout, $I$ is a finite set of agents and $A$ a set of alternatives; a valuation profile $v = (v_i)_{i \in I}$ gives each agent a valuation $v_i : A \to \mathbb{R}$, and $(w, v_{-i})$ denotes the profile $v$ with $v_i$ replaced by $w$.
For an alternative rule $f$ (from profiles to alternatives) and pivot terms $h_i$ (real functions of
profiles, one for each agent), the Groves payment of agent $i$ at the reported profile $v$ is

$$p_i(v) = h_i(v) - \sum_{j \neq i} v_j(f(v)) = h_i(v) - W_{-i}(v, f(v))$$

(Nisan 2007, Definition 9.16).
