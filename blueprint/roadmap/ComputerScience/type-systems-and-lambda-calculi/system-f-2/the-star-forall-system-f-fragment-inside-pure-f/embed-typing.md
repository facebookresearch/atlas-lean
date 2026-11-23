# Embedding preserves System F typing

Let $\Gamma$ be a System F term context, $t \in \mathrm{Tm}_{n,m}$ and $A \in \mathrm{Ty}_n$ with
$\Gamma \vdash t : A$ ([System F
typing](../../system-f/the-five-typing-rules-of-pure-system-f/typing.md)). Then $\mathcal{E}(\Gamma)
\vdash \mathcal{E}(t) : \mathcal{E}(A)$ in pure Fω
([typing](../pure-f-typing-with-proved-type-beta-conversion/typing.md)), where
$\mathcal{E}(\Gamma)(i) = \mathcal{E}(\Gamma(i))$ ([type embedding](embed.md), [term
embedding](embed-2.md)).
