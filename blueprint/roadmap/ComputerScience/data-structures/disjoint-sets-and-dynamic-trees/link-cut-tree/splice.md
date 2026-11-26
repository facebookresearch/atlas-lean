# Preferred-child switch at an auxiliary root

Replace its ordinary right subtree by the
already exposed suffix (absent in the first iteration). The detached child's up-pointer now
serves as a path-parent pointer; the incoming suffix's existing path-parent pointer now serves
as an ordinary parent pointer. Only the root record needs a write and aggregate repair.
