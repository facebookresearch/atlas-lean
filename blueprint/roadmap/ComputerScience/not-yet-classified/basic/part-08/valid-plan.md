# Valid Plan

A plan is valid for a task, in Bylander's total `Result` semantics, when
executing it from the initial state by `Operator.result` reaches a goal
state. Inapplicable operators in the plan are identity steps.
