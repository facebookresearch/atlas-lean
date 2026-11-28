# States from a program

`StateIn P s` says that the state `s` comes from the program `P`,
in one of two cases. An evaluating state `ev e env k` comes from `P` when `e` is a subterm of `P`,
its environment comes from `P` (`EnvIn P env`) and its continuation comes from `P`
(`KontIn P k`). A returning state `ret v k` has no control term or environment of its own: it comes
from `P` when the returned closure comes from `P` (`ClosIn P v`) and its continuation comes from
`P` (`KontIn P k`).
