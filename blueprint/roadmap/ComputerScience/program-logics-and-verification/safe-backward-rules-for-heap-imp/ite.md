# Ite

For a Boolean guard, heap commands `t`, `e` and heap postcondition
`Q`, suppose at an initial store and heap that a true guard implies
`safePre t Q` and a false guard implies `safePre e Q`. Then
`safePre (.ite guard t e) Q` holds there. Only the selected branch needs
to establish the postcondition safely.
