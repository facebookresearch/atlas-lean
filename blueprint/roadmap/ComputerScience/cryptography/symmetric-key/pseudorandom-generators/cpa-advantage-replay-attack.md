# The stream cipher is not CPA-secure

For every generator and messages $m_0 \neq m_1$, the one-query replay attack wins the CPA
indistinguishability experiment against the stream cipher with probability $1$, so its CPA advantage
is $\tfrac{1}{2}$, the maximum. More generally, no correct scheme with deterministic encryption and
at least two messages is CPA-secure (Katz and Lindell, Section 3.4.2; stated here without proof).
