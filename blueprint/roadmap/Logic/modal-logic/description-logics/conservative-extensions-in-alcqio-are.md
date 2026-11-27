# Conservative extensions in ALCQIO are undecidable

Deciding whether adding one TBox to another conservatively extends it, so that no new subsumptions between concepts of a given signature follow, is undecidable in the description logic ALCQIO with number restrictions, inverse roles and nominals.

**ALCQIO.** Concepts extend those of [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md) by *number restrictions* $(\leq n\; r\; C)$, interpreted as the set of $d$ with at most $n$ elements $e \in C^{\mathcal{I}}$ such that $(d, e) \in r^{\mathcal{I}}$ ($n$ in binary), *inverse roles* $r^-$ with $(r^-)^{\mathcal{I}} = \{(e, d) : (d, e) \in r^{\mathcal{I}}\}$, usable wherever roles are, and *nominals* $\{a\}$ for individual names $a$, interpreted as $\{a^{\mathcal{I}}\}$. A TBox is a finite set of concept inclusions $C \sqsubseteq D$; $\mathcal{T} \models C \sqsubseteq D$ means that $C^{\mathcal{I}} \subseteq D^{\mathcal{I}}$ in every model of $\mathcal{T}$. A *signature* is a finite set of concept, role and individual names, $\mathrm{sig}(\mathcal{T})$ is the set of names occurring in $\mathcal{T}$, and $\mathcal{L}(\Gamma)$ is the set of concepts of the logic $\mathcal{L}$ using only names from $\Gamma$.

**Conservative extensions.** For TBoxes $\mathcal{T}_1, \mathcal{T}_2$ of a description logic $\mathcal{L}$ and a signature $\Gamma \subseteq \mathrm{sig}(\mathcal{T}_1)$, $\mathcal{T}_1 \cup \mathcal{T}_2$ is a *$\Gamma$-conservative extension* of $\mathcal{T}_1$ if for all $C_1, C_2 \in \mathcal{L}(\Gamma)$, $\mathcal{T}_1 \models C_1 \sqsubseteq C_2$ iff $\mathcal{T}_1 \cup \mathcal{T}_2 \models C_1 \sqsubseteq C_2$; for $\Gamma = \mathrm{sig}(\mathcal{T}_1)$ it is a conservative extension.

**Theorem (Lutz, Walther and Wolter).** In ALCQIO it is undecidable, given TBoxes $\mathcal{T}_1, \mathcal{T}_2$ and a signature $\Gamma \subseteq \mathrm{sig}(\mathcal{T}_1)$, whether $\mathcal{T}_1 \cup \mathcal{T}_2$ is a $\Gamma$-conservative extension of $\mathcal{T}_1$ (Theorem 17). This holds even for $\Gamma = \mathrm{sig}(\mathcal{T}_1)$ and with $(\leq 1\; r\; \top)$ as the only number restriction.

In ALCQI, without nominals, the problem is 2EXPTIME-complete. If conservative extensions are defined model-theoretically instead, the problem is highly undecidable already in ALC.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)

## Proof depends on

None.

## Expansion

The proof reduces a domino (tiling) problem: from a domino system $\mathcal{D}$ it builds TBoxes $\mathcal{T}_1$ and $\mathcal{T}_2$ such that $\mathcal{D}$ has a solution iff $\mathcal{T}_1 \cup \mathcal{T}_2$ is not a conservative extension of $\mathcal{T}_1$, with models of witness concepts corresponding to solutions. The source says the undecidability of the domino problem used follows by known proof methods; a good expansion would link that variant of the tiling problem, which has no page.

## Sources

- C. Lutz, D. Walther and F. Wolter, "Conservative extensions in expressive description logics", in *Proceedings of the 20th International Joint Conference on Artificial Intelligence (IJCAI 2007)*, 2007, pp. 453–458; read in the open-access proceedings copy at [www.ijcai.org copy](https://www.ijcai.org/Proceedings/07/Papers/071.pdf): Section 2 (ALCQIO, Definition 1), Section 4 (Theorem 17 and the domino reduction) and the abstract.
