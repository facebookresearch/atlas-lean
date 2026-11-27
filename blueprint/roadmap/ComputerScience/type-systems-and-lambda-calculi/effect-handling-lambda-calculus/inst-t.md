# Instantiating the bound variable of a packaged term

Instantiating by a value `v`
substitutes `v` for index `0` of a value (`Val.inst`) or of a computation (`Comp.inst`);
instantiating by a computation, which binds nothing, is the identity. Part of the packaging of
the two sorts for `structuralTyping`.
