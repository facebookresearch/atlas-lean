# Weakening a packaged term

For any two contexts `Γ` and `Γ'`, `wkT Γ Γ' t` shifts every
free variable of the value or computation `t` up by `Γ'.length - Γ.length`, the length of the
target context minus the length of the source context in truncated subtraction of natural
numbers: the shift is `0` when `Γ'` is not longer than `Γ`. Part of the packaging of the two
sorts for `structuralTyping`.
