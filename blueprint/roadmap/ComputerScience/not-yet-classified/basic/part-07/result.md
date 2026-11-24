# Result

Bylander's total one-step result: apply an applicable operator, and leave
the state unchanged if its preconditions fail. `Task.ResultExecutes` and
`Task.ValidPlan` use this total step; `Task.Executes` and `Task.toLTS`
retain the strict applicable-only view.
