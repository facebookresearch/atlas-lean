# TO-security for intransitive information flow policies

TO-security, van der Meyden's semantics for intransitive noninterference, requires each domain's observation to depend only on what the domains allowed to interfere with it have actually observed and transmitted, as recorded by their views.

**Policies and machines.** A *noninterference policy* is a reflexive relation $\rightarrowtail \subseteq D \times D$ on a set $D$ of security domains, possibly not transitive; $u \rightarrowtail v$ means that $u$ may interfere with $v$. A *(state-observed) machine* is $M = \langle S, s_0, A, \mathrm{step}, \mathrm{obs}, \mathrm{dom} \rangle$ with states $S$, initial state $s_0$, actions $A$, a deterministic transition function $\mathrm{step} \colon S \times A \to S$, an observation function $\mathrm{obs} \colon S \times D \to O$ (written $\mathrm{obs}_u(s)$) and a domain assignment $\mathrm{dom} \colon A \to D$. Write $s \cdot \alpha$ for the state reached from $s$ by the action sequence $\alpha \in A^*$. $M$ is *finite-state* if $S$, $A$, $D$ and $O$ are finite.

**Views.** With the absorptive concatenation $\sigma \hat{\cdot} x = \sigma$ if $x$ is the last element of $\sigma$ and $\sigma \cdot x$ otherwise, the *view* of domain $u$ is

$$
\mathrm{view}_u(\epsilon) = \mathrm{obs}_u(s_0), \qquad \mathrm{view}_u(\alpha a) = (\mathrm{view}_u(\alpha) \cdot b)\ \hat{\cdot}\ \mathrm{obs}_u(s_0 \cdot \alpha a),
$$

where $b = a$ if $\mathrm{dom}(a) = u$ and $b = \epsilon$ otherwise: the record of $u$'s own actions and its observations with stuttering removed. (This is van der Meyden's definition; the extended version cited below prints $s_0 \cdot \alpha$ in place of $s_0 \cdot \alpha a$ in the last observation.)

**Transmitted information.** Define $\mathrm{to}_u(\epsilon) = \mathrm{obs}_u(s_0)$ and

$$
\mathrm{to}_u(\alpha a) = \begin{cases} \mathrm{to}_u(\alpha) & \text{if } \mathrm{dom}(a) \not\rightarrowtail u, \\ (\mathrm{to}_u(\alpha), \mathrm{view}_{\mathrm{dom}(a)}(\alpha), a) & \text{otherwise.} \end{cases}
$$

**Definition.** $M$ is *TO-secure* with respect to $\rightarrowtail$ if for all domains $u \in D$ and all $\alpha, \alpha' \in A^*$ with $\mathrm{to}_u(\alpha) = \mathrm{to}_u(\alpha')$ we have $\mathrm{obs}_u(s_0 \cdot \alpha) = \mathrm{obs}_u(s_0 \cdot \alpha')$.

The definitions of TA- and TO-security are due to van der Meyden (ESORICS 2007), as the source recalls.

## Depends on

None.

## Proof depends on

None.

## Expansion

TO-security sits between Haigh and Young's IP-security (via the intransitive purge) and van der Meyden's TA-security, whose function $\mathrm{ta}$ lets an action transmit everything its domain *may* know; $\mathrm{to}$ lets it transmit only what its domain has actually observed, its view. The motivating example is a downgrader policy $H \rightarrowtail D \rightarrowtail L$ in which $L$ learns about an action of $H$ only after $D$ acts, but $D$ itself never observes anything: the system is TA-secure, since $D$ may know the secret, yet not TO-secure. Van der Meyden's characterization: $M$ is TO-secure iff for all $u$, all $\alpha, \alpha'$ with equal purges for $u$ and with equal "possibly transmitted views" for every $v \ne u$ with $v \rightarrowtail u$, the observations of $u$ agree.

## Sources

- Sebastian Eggert, Ron van der Meyden, Henning Schnoor and Thomas Wilke, "The Complexity of Intransitive Noninterference", in *2011 IEEE Symposium on Security and Privacy (S&P 2011)*, IEEE Computer Society, 2011, pp. 196–211, <https://doi.org/10.1109/SP.2011.30>; read as the extended version arXiv:1308.1204v1, "Complexity and Unwinding for Intransitive Noninterference", <https://arxiv.org/abs/1308.1204v1>: Section 2 (noninterference policies, the state-observed machine model, and the subsection on the function to with the definition of TO-security and its characterization) of that version.
