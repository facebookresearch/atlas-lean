# Seq

For any heap commands `c₁`, `c₂` and heap postcondition `Q`,
`safePre c₁ (safePre c₂ Q)` entails `safePre (.seq c₁ c₂) Q`.
This is a sufficient backward rule for safe partial correctness.
