# Binding a variable of a packaged type

Binding at a value type `A` adds an innermost
variable of type `A`; binding at a computation type leaves the context unchanged, since
fine-grain call-by-value has no computation variables. Part of the packaging of the two sorts
for `structuralTyping`.
