# In Roth's market every stable mechanism is manipulable

Roth's market has three men $m_1, m_2, m_3$ and three women $w_1, w_2, w_3$.
Let $h$ be a matching mechanism for three men and three women whose outcome is stable for every stated
profile. At Roth's profile $P$, either man $m_1$ obtains a partner he truly prefers by reporting
$w_2 \succ w_3 \succ w_1$ (the others stating $P$), or woman $w_1$ obtains a partner she truly prefers by
reporting $m_1 \succ m_2 \succ m_3$.

Proof, following Roth. If $h(P)$ matches $m_1$ with $w_1$, then $m_1$ reports $w_2 \succ w_3 \succ w_1$; the
only stable matching of the resulting profile is $x$, which gives him $w_2$, his true first choice.
Otherwise $w_1$ is not matched with $m_1$, her true first choice; she reports $m_1 \succ m_2 \succ m_3$, and
the only stable matching of the resulting profile is $y$, which gives her $m_1$. Roth phrases the case split
as $h(P) = x$ or $h(P) = y$; splitting on $m_1$'s partner directly avoids the description of the stable set
of $P$.

## Informally uses

- [After $m_1$'s misreport, $x$ is the unique stable matching](roth-is-stable-man-misreport-iff.md): the outcome of the mechanism after $m_1$'s misreport.
- [After $w_1$'s misreport, $y$ is the unique stable matching](roth-is-stable-woman-misreport-iff.md): the outcome of the mechanism after $w_1$'s misreport.

## Background

- [Roth's market has exactly the two stable matchings $x$ and $y$](roth-is-stable-iff.md): the stable set of the true profile, as Roth describes it.

## Sources

- A. E. Roth, "The economics of matching: stability and incentives", *Mathematics of Operations Research* 7(4) (1982), 617–628, proof of Theorem 3.
