# CPA security

**CPA security** of a family of public-key schemes against all adversary families satisfying
`Admissible` (Katz and Lindell, Definition 11.2). Public-key CPA adversaries make no oracle
queries, so no query-count class applies; pass the intended class explicitly. With an
admissible class that bounds only queries (for example `PolyQueryBounded`), every adversary family
is admissible, so the result is security against unbounded adversaries, not the PPT notion of
Definition 11.2. The message and coin types must be nonempty (`PubCPAAdversary.nonempty`); whether
some family is admissible depends on `Admissible`.
